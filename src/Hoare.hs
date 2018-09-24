{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
module Hoare where

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
  deriving (Show, Read, Eq, Ord)

cvocab :: Com -> Set Var
cvocab = \case
  Skip -> S.empty
  Assign v e -> S.insert v (evocab e)
  If p c1 c2 -> S.unions [pvocab p, cvocab c1, cvocab c2]
  Seq c1 c2 -> cvocab c1 `S.union` cvocab c2
  While p c -> pvocab p `S.union` cvocab c

mkRel :: MonadState Integer m => Set Var -> m Prop
mkRel voc = do
  c <- get
  put (c+1)
  pure $ PRel ("$rel" ++ show c) (map V $ S.toList voc)

clause :: Prop -> Prop -> Prop
clause pre post =
  foldr PForall (PImpl pre post) (pvocab (PAnd pre post))

hoare' :: Com -> Prop -> StateT Integer (Writer [Prop]) Prop
hoare' c q =
  case c of
    Skip -> pure q
    Assign v e -> pure (psubst v e q)
    If cond c1 c2 -> do
      p <- mkRel (cvocab c `S.union` pvocab q)
      q0 <- hoare' c1 q
      q1 <- hoare' c2 q
      tell [ clause (PAnd p cond) q0
           , clause (PAnd p (PNot cond)) q1
           ]
      pure p
    Seq c1 c2 -> hoare' c1 =<< hoare' c2 q
    While cond c0 -> do
      p <- mkRel (cvocab c `S.union` pvocab q)
      r <- hoare' c0 p
      tell [ clause (PAnd p cond) r
           , clause (PAnd p (PNot cond)) q
           ]
      pure p
    Assert cond -> pure cond

hoare :: Com -> [Prop]
hoare c = case runWriter (evalStateT (hoare' c PTrue) 0) of
            (p, ps) -> foldr PForall p (pvocab p) : ps

example :: Com
example =
  Assign "x" (Lit 0) `Seq`
  While (PLt (V "x") (V "n"))
    (Assign "x" (Add (V "x") (Lit 2))) `Seq`
  Assert (PNot (PEql (V "x") (Lit 41)))
