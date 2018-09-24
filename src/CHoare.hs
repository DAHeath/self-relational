{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
module CHoare where

import           Control.Monad.State
import           Control.Monad.Writer
import qualified Data.Set as S
import           Data.Set (Set)

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
  | PProd Prop Prop {- NEW -}
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
  PProd p1 p2 -> pvocab p1 `S.union` pvocab p2

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
  PProd p1 p2 -> PProd (psubst v e p1) (psubst v e p2)

data Com
  = Skip
  | Assign Var Expr
  | If Prop Com Com
  | Seq Com Com
  | While Prop Com
  | Assert Prop
  | Prod Com Com {- NEW -}
  deriving (Show, Read, Eq, Ord)

{- NEW -}
isSimple :: Com -> Bool
isSimple = \case
  While{} -> False
  If _ c0 c1 -> isSimple c0 && isSimple c1
  Seq c0 c1 -> isSimple c0 && isSimple c1
  Prod c0 c1 -> isSimple c0 && isSimple c1
  _ -> True

cvocab :: Com -> Set Var
cvocab = \case
  Skip -> S.empty
  Assign v e -> S.insert v (evocab e)
  If p c1 c2 -> S.unions [pvocab p, cvocab c1, cvocab c2]
  Seq c1 c2 -> cvocab c1 `S.union` cvocab c2
  While p c -> pvocab p `S.union` cvocab c
  Prod c1 c2 -> cvocab c1 `S.union` cvocab c2

mkRel :: MonadState Integer m => Set Var -> m Prop
mkRel voc = do
  c <- get
  put (c+1)
  pure $ PRel ("$rel" ++ show c) (map V $ S.toList voc)

clause :: Prop -> Prop -> Prop
clause pre post =
  foldr PForall (PImpl pre post) (pvocab (PAnd pre post))

-- Partition the command such that each part (except the first!) has a
-- non-simple command as its first element.
partition :: Com -> [Com]
partition (Seq (Seq c0 c1) c2) = partition (Seq c0 (Seq c1 c2))
partition (Seq c0 c1) =
  let p:ps = partition c1 in
  if isSimple c0
   then Seq c0 p:ps
   else Skip:Seq c0 p:ps
partition c =
  if isSimple c then [c] else [Skip, c]

hoare' :: (Com, Prop) -> StateT Integer (Writer [Prop]) (Com, Prop)
hoare' (c, q) =
  case c of
    Skip -> pure (Skip, q)
    Assign v e -> pure (Skip, psubst v e q)
    If cond c1 c2 ->
      if isSimple c then do
        p <- mkRel (cvocab c `S.union` pvocab q)
        (_, q0) <- hoare' (c1, q)
        (_, q1) <- hoare' (c2, q)
        tell [ clause (PAnd p cond) q0
             , clause (PAnd p (PNot cond)) q1
             ]
        pure (Skip, p)
      else pure (c, q)
    Seq (Seq c0 c1) c2 -> hoare' (Seq c0 (Seq c1 c2), q)
    Seq c0 c1 -> do
      (_, r) <- hoare' (c1, q)
      hoare' (c0, r)
    While{} -> pure (c, q)
    Assert cond -> pure (Skip, cond)

-- TESTING
hoare :: Com -> IO [Prop]
hoare c = case runWriter (evalStateT (hoare' (c, PTrue)) 0) of
            ((c, p), ps) -> do
              print c
              pure (foldr PForall p (pvocab p) : ps)

choare' :: Com -> Prop -> StateT Integer (Writer [Prop]) Prop
choare' c q =
  case c of
    Skip -> pure q
    Assign v e -> pure (psubst v e q)
    Assert cond -> pure cond

example :: Com
example =
  Assign "sum0" (Lit 0) `Seq`
  Assign "i" (Lit 0) `Seq`
  While (PLt (V "i") (V "n"))
    ( Assign "sum0" (Add (V "sum0") (V "i")) `Seq`
      Assign "i" (Add (V "i") (Lit 1))
    ) `Seq`
  Assign "sum1" (Lit 0) `Seq`
  Assign "i" (Sub (V "n") (Lit 1)) `Seq`
  While (PLt (Lit 0) (V "i"))
    ( Assign "sum1" (Add (V "sum1") (V "i")) `Seq`
      Assign "i" (Sub (V "i") (Lit 1))
    ) `Seq`
  Assert (PNot (PEql (V "x") (Lit 41)))
