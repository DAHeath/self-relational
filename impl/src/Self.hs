{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
module Self where

import Control.Monad.State
import Control.Monad.Except

newtype Var = Var { getVar :: String }
  deriving (Show, Read, Eq, Ord)

data Expr
  = ALit Integer
  | Add Expr Expr
  deriving (Show, Read, Eq, Ord)

data Prop
  = T
  | F
  | And Prop Prop
  deriving (Show, Read, Eq, Ord)

data Com
  = Assign Var Expr
  | Assert Prop
  | Skip
  | Seq Com Com
  | Sum Com Com
  | Prod Com Com
  | Loop Com
  deriving (Show, Read, Eq, Ord)

data Error = Error

type M a = StateT Int (Either Error) a

fresh :: M Prop
fresh = undefined

pairwise :: Prop -> Prop -> Prop
pairwise = undefined

clause :: Prop -> Prop -> M ()
clause = undefined

subst = undefined

loopless :: Com -> Bool
loopless = undefined

allLoops :: Com -> Bool
allLoops = undefined

dispatch :: Com -> Prop -> M Prop
dispatch c q =
  case c of
    Assign x e ->
      pure (subst x e q)
    Assert e -> do
      p <- fresh
      clause (And p e) q
      pure p
    Skip -> pure q
    Seq c0 c1 -> do
      r <- fresh
      p <- dispatch c0 r
      pr <- dispatch (Prod c0 c1) (pairwise r q)
      clause (pairwise p r) pr
      pure p
    Sum c0 c1 -> do
      p <- fresh
      p0 <- dispatch c0 q
      p1 <- dispatch c1 q
      clause p p0
      clause p p1
      pure p
    Prod c0 c1 -> do
      if | loopless c0 || loopless c1 -> do
           q0 <- fresh
           q1 <- fresh
           p0 <- dispatch c0 q0
           p1 <- dispatch c1 q1
           p <- fresh
           clause p p0 -- TODO
           clause p p1 -- TODO
           clause (pairwise q0 q1) q -- TODO
           pure p
         -- | allLoops c0 && allLoops c1 -> do
         --   p <- fresh
         --   let c0
         | otherwise ->
           case (c0, c1) of
             (Sum c0' c0'', _) -> dispatch (Sum (Prod c0' c1) (Prod c0'' c1)) q
             (_, Sum c1' c1'') -> dispatch (Sum (Prod c0 c1') (Prod c0 c1'')) q
             (Seq c0' c0'', Seq c1' c1'') -> dispatch (Seq (Prod c0' c1') (Prod c0'' c1'')) q
    Loop c0 -> do

