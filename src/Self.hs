{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
module Self where

import Control.Lens
import Control.Monad.State
import Control.Monad.Writer hiding (Sum)
import Control.Monad.Reader
import Control.Monad.Except
import qualified Data.Set as S
import           Data.Set (Set)
import qualified Data.Map as M
import           Data.Map (Map)
import Data.Foldable
import Prelude hiding (pred)

import Debug.Trace

type Var = String

-- | The space of arithmetic expressions.
data Expr
  = ALit Integer
  | Add Expr Expr
  | V Var
  deriving (Show, Read, Eq, Ord)

vrename :: Int -> Var -> Var
vrename c v = (v ++ "_" ++ show c)

esubst :: Var -> Expr -> Expr -> Expr
esubst x e = \case
  ALit i -> ALit i
  Add e0 e1 -> Add (go e0) (go e1)
  V v -> if v == x then e else V v
  where
    go = esubst x e

erename :: Int -> Expr -> Expr
erename c = \case
  ALit i -> ALit i
  V v -> V (vrename c v)
  Add a0 a1 -> Add (erename c a0) (erename c a1)

evocab :: Expr -> Set Var
evocab = \case
  V v -> S.singleton v
  Add e0 e1 -> S.union (evocab e0) (evocab e1)
  ALit{} -> S.empty

type ID = Int

-- | The space of (quantifier-free) logical propositions.
data Prop
  = T
  | F
  | Not Prop
  | And Prop Prop
  | Impl Prop Prop
  | Eql Expr Expr
  | Lt Expr Expr
  | Ge Expr Expr
  | Rel ID [Expr]
  deriving (Show, Read, Eq, Ord)

pmap :: (Expr -> Expr) -> Prop -> Prop
pmap f = \case
  T -> T
  F -> F
  Not p -> Not (go p)
  And p0 p1 -> And (go p0) (go p1)
  Impl p0 p1 -> Impl (go p0) (go p1)
  Eql e0 e1 -> Eql (f e0) (f e1)
  Lt e0 e1 -> Lt (f e0) (f e1)
  Ge e0 e1 -> Ge (f e0) (f e1)
  Rel i es -> Rel i (map f es)
  where
    go = pmap f

psubst :: Var -> Expr -> Prop -> Prop
psubst x e = pmap (esubst x e)

prename :: Int -> Prop -> Prop
prename i = pmap (erename i)

pvocab :: Prop -> Set Var
pvocab = \case
  T -> S.empty
  F -> S.empty
  Not p -> pvocab p
  And p0 p1 -> S.union (pvocab p0) (pvocab p1)
  Impl p0 p1 -> S.union (pvocab p0) (pvocab p1)
  Eql e0 e1 -> S.union (evocab e0) (evocab e1)
  Lt e0 e1 -> S.union (evocab e0) (evocab e1)
  Ge e0 e1 -> S.union (evocab e0) (evocab e1)
  Rel _ es -> S.unions (map evocab es)

pand :: Prop -> Prop -> Prop
pand T p = p
pand p T = p
pand F _ = F
pand _ F = F
pand p q = p `And` q

pimpl :: Prop -> Prop -> Prop
pimpl T p = p
pimpl p q = p `Impl` q

prels :: Prop -> Set (ID, Int)
prels = \case
  T -> S.empty
  F -> S.empty
  Not p -> prels p
  And p0 p1 -> prels p0 `S.union` prels p1
  Impl p0 p1 -> prels p0 `S.union` prels p1
  Eql{} -> S.empty
  Lt{} -> S.empty
  Ge{} -> S.empty
  Rel i es -> S.singleton (i, length es)

-- | The space of non-deterministic imperative commands.
data Com
  = Assign Var Expr
  | Assert Prop
  | Skip
  | Seq Com Com
  | Sum Com Com
  | Prod Com Com
  | Loop Com
  deriving (Show, Read, Eq, Ord)

cvocab :: Com -> Set Var
cvocab = \case
  Assign v e -> S.insert v $ evocab e
  Assert p -> pvocab p
  Skip -> S.empty
  Seq c0 c1 -> cvocab c0 `S.union` cvocab c1
  Sum c0 c1 -> cvocab c0 `S.union` cvocab c1
  Prod c0 c1 -> cvocab c0 `S.union` cvocab c1
  Loop c -> cvocab c

loopless :: Com -> Bool
loopless = \case
  Loop{} -> False
  Sum c0 c1 -> loopless c0 && loopless c1
  Prod c0 c1 -> loopless c0 && loopless c1
  Seq c0 c1 -> loopless c0 && loopless c1
  Assert{} -> True
  Assign{} -> True
  Skip -> True

mergeLoops :: Com -> Com
mergeLoops = \case
  Prod c0 c1 ->
    let c0' = mergeLoops c0
        c1' = mergeLoops c1
    in case (c0', c1') of
         (Loop c0, Loop c1) -> Loop (Prod (Sum c0 Skip) (Sum c1 Skip))
         _ -> Prod c0' c1'
  c -> c

type Vocab = [Var]

type Token = Int

data St = Singleton Token | Composite St St
  deriving (Show, Read, Eq, Ord)

data Env = Env
  { _vocab :: Vocab
  , _theState :: St
  , _stateCount :: Int
  , _quantifiedState :: [St]
  }
makeLenses ''Env

initialEnv :: Com -> Env
initialEnv c =
  let v =  S.toList $ cvocab c
  in Env
     { _vocab = v
     , _theState = Singleton 0
     , _stateCount = 1
     , _quantifiedState = []
     }

data QProp = Forall [Var] Prop
  deriving (Show, Read, Eq, Ord)

quantify :: Prop -> QProp
quantify p = Forall (S.toList (pvocab p)) p

data Ctxt = Ctxt
  { _relCount :: Int
  , _stubCount :: Int
  , _stubs :: Map Int Assertion
  }

type Stub = Int
type Pred = Int

data Assertion
  = ASSIGN Var Expr
  | ASSERT Prop
  | STUB Stub
  | PRED Pred
  | THEN Assertion Assertion
  | PAIRWISE Assertion Assertion
  | TRUE
  deriving (Show, Read, Eq, Ord)

makeLenses ''Ctxt

initialCtxt :: Ctxt
initialCtxt = Ctxt 0 0 M.empty

assertion :: St -> Assertion -> M Prop
assertion = go T
  where
    go p (Singleton t) (ASSIGN x e) = pure $ psubst (vrename t x) (erename t e) p
    go p (Singleton t) (ASSERT q) = pure $ p `pand` prename t q
    go p st (STUB n) = (go p st =<< uses stubs (M.findWithDefault TRUE n))
    go p st (PRED n) = pand p <$> predicate st n
    go p st (THEN x y) = (\q -> go q st x) =<< go p st y
    go p (Composite st0 st1) (PAIRWISE x y) = go p st0 x >>= (\q -> go q st1 y)
    go p _ TRUE = pure p
    go _ _ _ = undefined

assignments :: St -> Assertion -> M (Prop -> Prop)
assignments = go
  where
    go (Singleton t) (ASSIGN x e) = pure $ psubst (vrename t x) (erename t e)
    go (Singleton t) (ASSERT q) = pure id
    go st (STUB n) = go st =<< uses stubs (M.findWithDefault TRUE n)
    go st (PRED n) = pure id
    go st (THEN x y) = do
      f <- go st y
      g <- go st x
      pure (g . f)
    go (Composite st0 st1) (PAIRWISE x y) = do
      f <- go st0 x
      g <- go st1 y
      pure (g . f)
    go _ TRUE = pure id
    go _ _ = undefined

predicate :: St -> Int -> M Prop
predicate st c = do
  v <- view vocab
  let v' = map V v
  q <- view quantifiedState
  let ts = concatMap flatten (st : q)
  let es = concatMap (\t -> map (erename t) v') ts
  pure (Rel c es)
    where
      flatten :: St -> [Token]
      flatten = \case
        Singleton t -> [t]
        Composite st0 st1 -> flatten st0 ++ flatten st1

(<=>) :: Assertion -> Stub -> M ()
(<=>) b i = stubs %= M.insert i b

(==>) :: Assertion -> Pred -> M ()
(==>) b c = do
  st <- view theState
  b' <- assertion st b
  f <- assignments st b
  h' <- predicate st c
  tell [quantify $ b' `pimpl` f h']

type M a = ReaderT Env (StateT Ctxt (Writer [QProp])) a

stub :: M Stub
stub = stubCount <<+= 1

pred :: M Pred
pred = relCount <<+= 1

-- equiv :: Vocab -> St -> St -> Prop
-- equiv v (Composite st0 st1) (Composite st2 st3) = equiv v st0 st2 `pand` equiv v st1 st3
-- equiv v (Singleton i st0) (Singleton j st1) =
--   foldr (\v p -> eq1 i j st0 st1 v `pand` p) T v
--   where
--     eq1 i j st0 st1 v = erename i (st0 (V v)) `Eql` erename j (st1 (V v))

commute, associate, left, right, double :: M a -> M a

commute = local (theState %~ go)
  where go (Composite st0 st1) = Composite st1 st0

associate = local (theState %~ go)
  where go (Composite st0 (Composite st1 st2)) = Composite (Composite st0 st1) st2

left ac = do
  Composite st0 st1 <- view theState
  local ( (quantifiedState %~ (st0 :))
        . (theState .~ st1)
        ) ac

right ac = do
  Composite st0 st1 <- view theState
  local ( (quantifiedState %~ (st1 :))
        . (theState .~ st0)
        ) ac

double ac = do
  c <- view stateCount
  st <- view theState
  let (st', c') = runState (go st) c
  local ((stateCount .~ c') . (theState .~ (st `Composite` st'))) ac
  where
    go :: St -> State Int St
    go (Singleton st) = do
      c <- id <<+= 1
      pure (Singleton c)
    go (Composite st0 st1) = Composite <$> go st0 <*> go st1

triple :: Assertion -> Com -> Stub -> M ()
triple p c q =
  case mergeLoops c of
    Skip -> p <=> q
    Assign x a -> THEN p (ASSIGN x a) <=> q
    Assert e -> THEN p (ASSERT e) <=> q
    Seq c0 c1 -> do
      if loopless c0 || loopless c1
      then do
        r <- stub
        triple p c0 r
        triple (STUB r) c1 q
      else do
        undefined
        -- v <- view vocab
        -- localDouble (do
        --   r <- rel
        --   s <- rel
        --   q' <- rel
        --   localRight (\st0 -> triple (p /\ equiv v st0) c0 (left st0 r))
        --   post <- localLeft (\st1 -> do
        --     triple (right st1 s) c1 (right st1 q')
        --     right st1 q' /\ equiv v st1 ==> q)
        --   triple r (Prod c0 c1) s)
    Sum c0 c1 -> do
      q0 <- stub
      q1 <- stub
      r <- pred
      triple p c0 q0
      triple p c1 q1
      STUB q0 ==> r
      STUB q1 ==> r
      PRED r <=> q
    Loop c -> do
      r <- pred
      s <- stub
      p ==> r
      triple (PRED r) c s
      (STUB s) ==> r
      (PRED r) <=> q
    -- Prod c0 c1 ->
    --   if loopless c0 || loopless c1
    --   then do
    --     r <- rel
    --     localLeft (\st1 -> triple (right st1 p) c0 (right st1 r))
    --     localRight (\st0 -> triple (left st0 r) c1 (left st0 q))
    --   else
    --     case c1 of
    --       Sum c1' c1'' -> triple p (Sum (Prod c0 c1') (Prod c0 c1'')) q
    --       Prod c1' c1'' -> localAssociate (triple (associate p) (Prod (Prod c0 c1') c1'') (associate q))
    --       Loop c1' -> localCommute (triple (commute p) (Prod (Loop c1') c0) (commute q))
    --       Seq c1' c1'' ->
    --         if loopless c1'
    --         then triple p (Seq (Prod Skip c1') (Prod c0 c1'')) q
    --         else triple p (Seq (Prod c0 c1') (Prod Skip c1'')) q
    --       _ -> error ("Some impossible state has been reached: `" ++ showCom c ++ "`.")

hoare :: Com -> [QProp]
hoare c =
  let ctx = initialEnv c
   in execWriter $ evalStateT (runReaderT
        (do
          q <- stub
          triple TRUE c q
          q' <- join $ assertion <$> view theState <*> pure (STUB q)
          st <- use stubs
          traceM $ show st
          tell [quantify $ q' `pimpl` F]) ctx) initialCtxt

showCom :: Com -> String
showCom = \case
  Skip -> "skip"
  Assign v e -> v ++ " := " ++ smt2Expr e
  Assert e -> "assert " ++ smt2Prop e
  Seq c0 c1 -> showCom c0 ++ ";\n" ++ showCom c1
  Sum c0 c1 -> "{" ++ showCom c0 ++ "} +\n {" ++ showCom c1 ++ "}"
  Prod c0 c1 -> "{" ++ showCom c0 ++ "} *\n {" ++ showCom c1 ++ "}"
  Loop c -> "LOOP {\n" ++ showCom c ++ "}"

sexpr :: [String] -> String
sexpr ss = "(" ++ unwords ss ++ ")"

smt2 :: Com -> String
smt2 c = unlines [header, decls, body, footer]
  where
    header = unlines [ sexpr ["set-logic", "HORN"]
                     , sexpr ["set-option", ":fixedpoint.engine", "\"duality\""]
                     ]
    footer = unlines [ sexpr ["check-sat"], sexpr ["get-model"] ]
    decl (i, n) = sexpr ["declare-fun", "R" ++ show i, sexpr (replicate n "Int"), "Bool"]
    decls = unlines $ map decl (S.toList rels)
    body = unlines (map smt2QProp qs)
    qs = hoare c
    rels = S.unions (map qrels qs)
    qrels (Forall _ p) = prels p

smt2QProp :: QProp -> String
smt2QProp (Forall vs p) = sexpr ["assert", body] ++ "\n"
  where
    body = case vs of
             [] -> smt2Prop p
             _ -> sexpr ["forall", (sexpr $ map var vs) ++ "\n", "  " ++ smt2Prop p]
    var v = sexpr [v, "Int"]

smt2Expr :: Expr -> String
smt2Expr = \case
  ALit i -> show i
  Add a0 a1 -> sexpr ["+", smt2Expr a0, smt2Expr a1]
  V v -> v

smt2Prop :: Prop -> String
smt2Prop = \case
  T -> "true"
  F -> "false"
  Not p -> sexpr ["not", smt2Prop p]
  And p0 p1 -> sexpr ["and", smt2Prop p0, smt2Prop p1]
  Impl p0 p1 -> sexpr ["=>", smt2Prop p0, smt2Prop p1]
  Eql e0 e1 -> sexpr ["=", smt2Expr e0, smt2Expr e1]
  Lt e0 e1 -> sexpr ["<", smt2Expr e0, smt2Expr e1]
  Ge e0 e1 -> sexpr [">=", smt2Expr e0, smt2Expr e1]
  Rel i es -> sexpr (("R" ++ show i) : map smt2Expr es)

example :: Com
example =
  Assign "x" (ALit 0) `Seq`
  Assign "x" (Add (V "x") (ALit 1)) `Seq`
  Assign "x" (Add (V "x") (ALit 1)) `Seq`
  Assert (Not (Eql (V "x") (ALit 2)))

example2 :: Com
example2 =
  Sum
    (Assign "x" (ALit 0))
    (Assign "x" (ALit 1))
  `Seq`
  Assert (Lt (V "x") (ALit 0))

example3 :: Com
example3 =
  Assign "s0" (ALit 0) `Seq`
  Assign "s1" (ALit 0) `Seq`
  Assign "i0" (ALit 0) `Seq`
  Assign "i1" (ALit 0) `Seq`
  Loop (
    Assert (Lt (V "i0") (V "n")) `Seq`
    Assign "s0" (Add (V "s0") (V "i0")) `Seq`
    Assign "i0" (Add (V "i0") (ALit 1))
  ) `Seq`
  Assert (Ge (V "i0") (V "n")) `Seq`
  Loop (
    Assert (Lt (V "i1") (V "n")) `Seq`
    Assign "s1" (Add (V "s1") (V "i1")) `Seq`
    Assign "i1" (Add (V "i1") (ALit 1))
  ) `Seq`
  Assert (Ge (V "i1") (V "n")) `Seq`
  Assert (Not (Eql (V "s0") (V "s1")))

example4 :: Com
example4 =
  Assign "a" (ALit 0) `Seq`
  Assign "b" (ALit 0) `Seq`
  Loop (
    Assert (Lt (V "b") (V "n")) `Seq`
    Assign "b" (Add (V "b") (ALit 1)) `Seq`
    Assign "a" (Add (V "a") (V "b"))
  ) `Seq`
  Assert (Ge (V "b") (V "n")) `Seq`
  Assert (Lt (V "a") (V "n"))
