{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
module Hoare where

import           Control.Monad.State
import           Control.Monad.Writer
import qualified Data.Set as S
import           Data.Set (Set)
import qualified Data.Map as M
import           Data.Map (Map)

import Debug.Trace

type Var = String

data Expr
  = Add Expr Expr
  | Mul Expr Expr
  | Sub Expr Expr
  | Div Expr Expr
  | Lit Integer
  | V Var
  deriving (Show, Read, Eq, Ord)

evocab :: Expr -> Set Var
evocab = \case
  Add e1 e2 -> evocab e1 `S.union` evocab e2
  Mul e1 e2 -> evocab e1 `S.union` evocab e2
  Sub e1 e2 -> evocab e1 `S.union` evocab e2
  Div e1 e2 -> evocab e1 `S.union` evocab e2
  Lit _ -> S.empty
  V v -> S.singleton v

esubst :: Var -> Expr -> Expr -> Expr
esubst v e = \case
  Add e1 e2 -> Add (esubst v e e1) (esubst v e e2)
  Mul e1 e2 -> Mul (esubst v e e1) (esubst v e e2)
  Sub e1 e2 -> Sub (esubst v e e1) (esubst v e e2)
  Div e1 e2 -> Div (esubst v e e1) (esubst v e e2)
  Lit i -> Lit i
  V v' -> if v == v' then e else V v'

data Prop
  = PTrue
  | PFalse
  | PImpl Prop Prop
  | PAnd Prop Prop
  | PNot Prop
  | PEql Expr Expr
  | PLt Expr Expr
  | PRel Var [Expr]
  | PForall Var Prop
  deriving (Show, Read, Eq, Ord)

pvocab :: Prop -> Set Var
pvocab = \case
  PTrue -> S.empty
  PFalse -> S.empty
  PImpl p1 p2 -> pvocab p1 `S.union` pvocab p2
  PAnd p1 p2 -> pvocab p1 `S.union` pvocab p2
  PNot p -> pvocab p
  PEql e1 e2 -> evocab e1 `S.union` evocab e2
  PLt e1 e2 -> evocab e1 `S.union` evocab e2
  PRel v es -> S.unions (map evocab es)

psubst :: Var -> Expr -> Prop -> Prop
psubst v e = \case
  PTrue -> PTrue
  PFalse -> PFalse
  PImpl p1 p2 -> PImpl (psubst v e p1) (psubst v e p2)
  PAnd p1 p2 -> PAnd (psubst v e p1) (psubst v e p2)
  PNot p -> PNot (psubst v e p)
  PEql e1 e2 -> PEql (esubst v e e1) (esubst v e e2)
  PLt e1 e2 -> PLt (esubst v e e1) (esubst v e e2)
  PRel n es -> PRel n (map (esubst v e) es)

data Com
  = Skip
  | Assign Var Expr
  | If Prop Com Com
  | Seq Com Com
  | While Prop Com
  | Assert Prop
  | Prod Com Com
  | Fail
  deriving (Show, Read, Eq, Ord)

cvocab :: Com -> Set Var
cvocab = \case
  Skip -> S.empty
  Assign v e -> S.insert v (evocab e)
  If p c1 c2 -> S.unions [pvocab p, cvocab c1, cvocab c2]
  Seq c1 c2 -> cvocab c1 `S.union` cvocab c2
  Prod c1 c2 -> cvocab c1 `S.union` cvocab c2
  While p c -> pvocab p `S.union` cvocab c
  Fail -> S.empty

data HoareState = HoareState
  { counter :: Integer
  , relations :: Map Com Prop
  } deriving (Show, Read, Eq, Ord)

emptyHoareState :: HoareState
emptyHoareState = HoareState
  { counter = 0
  , relations = M.empty
  }

mkRel :: MonadState HoareState m => Com -> Set Var -> m Prop
mkRel c voc = do
  HoareState count rels <- get
  case M.lookup c rels of
    Nothing -> do
      let r = PRel ("$rel" ++ show count) (map V $ S.toList voc)
      put (HoareState (count+1) (M.insert c r rels))
      pure r
    Just r -> pure r

clause :: Prop -> Prop -> Prop
clause pre post =
  foldr PForall (PImpl pre post) (pvocab (PAnd pre post))

hoare' :: (MonadState HoareState m, MonadWriter [Prop] m)
      => Com
      -> Prop {- The post condition -}
      -> m Prop {- The pre condition -}
hoare' c q =
  case c of
    Skip -> pure q
    Prod{} -> do
      let v = S.union (pvocab q) (cvocab c)
      p <- mkRel c v
      cart' p c Skip q
      return p
    c ->
      cart c Skip q

cart' :: (MonadState HoareState m, MonadWriter [Prop] m)
      => Prop -> Com -> Com -> Prop -> m ()
cart' p c0 c1 q =
  case c0 of
    Prod c0' c0'' -> do
      cart' p c0' (mkProd c0'' c1) q
      cart' p c0'' (mkProd c0' c1) q
    c -> do
      p' <- cart c c1 q
      let v = S.union (pvocab p) (pvocab p')
      tell [clause p p']

cart :: (MonadState HoareState m, MonadWriter [Prop] m)
     => Com -> Com -> Prop -> m Prop
cart c0 c1 q =
  case c0 of
    Skip -> hoare' c1 q
    Assign x e -> hoare' c1 (psubst x e q)
    If e c0' c0'' -> do
      q' <- hoare' (mkProd c0' c1) q
      q'' <- hoare' (mkProd c0'' c1) q
      let v = S.unions [pvocab q, cvocab c0, cvocab c1]
      p <- mkRel (Prod c0 c1) v
      tell [ clause (PAnd p e) q'
           , clause (PAnd p (PNot e)) q''
           ]
      pure p
    While{} -> undefined -- TODO
    Seq c0' c0'' -> do
      let v = S.unions [pvocab q, cvocab c0, cvocab c1]
      p <- mkRel (Prod c0 c1) v
      mapM_ (\(p0, p1) ->
        when (p0 /= Skip && p1 /= Skip) $ do
          p' <- hoare' p0 =<< hoare' p1 q
          tell [clause p p']) (partitions (mkProd c0 c1))
      pure p
    Fail -> do
      let v = pvocab q
      p <- mkRel (Prod c0 c1) v
      tell [clause PFalse q]
      pure p
    Prod{} -> undefined

partitions :: Com -> [(Com, Com)]
partitions = \case
  Seq c0 c1 ->
    S.toList $ S.fromList $ concat
    [ [ (c0', mkSeq c0'' c1) | (c0', c0'') <- partitions c0 ]
    , [ (mkSeq c0 c1', c1'') | (c1', c1'') <- partitions c1 ]
    ]
  Prod c0 c1 -> do
    (p0, p0') <- partitions c0
    (p1, p1') <- partitions c1
    if or [ p0 == Skip && p1 == Skip
          , p0' == Skip && p1' == Skip
          , p0 == Skip && p1' == Skip
          , p1 == Skip && p0' == Skip
          ]
    then []
    else [(Prod p0 p1, Prod p0' p1')]
  c -> [ (c, Skip), (Skip, c) ]

mkSeq :: Com -> Com -> Com
mkSeq Skip c = c
mkSeq c Skip = c
mkSeq c0 c1 = Seq c0 c1

mkProd :: Com -> Com -> Com
mkProd Skip c = c
mkProd c Skip = c
mkProd c0 c1 = Prod c0 c1

hoare :: Com -> [Prop]
hoare c = case runWriter (evalStateT (hoare' c PTrue) emptyHoareState) of
            (p, ps) -> foldr PForall p (pvocab p) : ps

test :: Com
test =
  Prod
    ( Assign "a" (Lit 3)
    `Seq` Assign "b" (Lit 5)
    )
    ( Assign "c" (Lit 5)
    `Seq` Assign "d" (Lit 3)
    )
c0 :: Com
c0 = Assign "a" (Lit 3) `Seq` Assign "b" (Lit 5)

a, b :: Com
a = Assign "a" (Lit 3)
b = Assign "b" (Lit 5)
