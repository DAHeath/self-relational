{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
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

data St
  = SID Int
  | SPair St St
  deriving (Show, Read, Eq, Ord)

type ID = Int

data Tree a
  = Leaf a
  | Branch (Tree a) (Tree a)
  deriving (Functor, Show, Read, Eq, Ord)

type Shape = Tree ID

type Vocab = Tree [Var]

type Rename = Tree (Var -> Var)

data Assertion = Assertion
  { shape :: Shape
  , fact :: Rename -> Prop
  }

commute :: Assertion -> Assertion
commute (Assertion (Branch s0 s1) phi) =
  Assertion (Branch s1 s0)
            (\case
                Branch r0 r1 -> phi (Branch r1 r0)
                _ -> undefined)
commute _ = undefined

associate :: Assertion -> Assertion
associate (Assertion (Branch s0 (Branch s1 s2)) phi) =
  Assertion (Branch (Branch s0 s1) s2)
            (\case
                Branch r0 (Branch r1 r2) -> phi (Branch r0 (Branch r1 r2))
                _ -> undefined)
associate _ = undefined

mkAnd :: Assertion -> Assertion -> Assertion
mkAnd (Assertion s0 phi0) (Assertion _ phi1) =
  Assertion s0 (\r -> phi0 r `And` phi1 r)

pairwise :: Assertion -> Assertion -> Assertion
pairwise (Assertion s0 phi0) (Assertion s1 phi1) =
  Assertion (Branch s0 s1)
            (\case
              Branch r0 r1 -> And (phi0 r0) (phi1 r1)
              _ -> undefined)

type M a = State Int a

freshRel :: M Assertion
freshRel = undefined

clause :: Assertion -> Assertion -> M ()
clause = undefined

mkAssertion :: Prop -> Assertion
mkAssertion = undefined

andE :: Assertion -> Prop -> Assertion
andE a p = mkAnd a (mkAssertion p)

subst = undefined

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

dispatch :: Com -> Assertion -> M Assertion
dispatch c q =
  case c of
    Assign x e ->
      pure (subst x e q)
    Assert e -> do
      p <- freshRel
      clause (andE p e) q
      pure p
    Skip -> pure q
    Seq c0 c1 ->
      if loopless c0 || loopless c1
      then do
        r <- dispatch c1 q
        dispatch c0 r
      else do
        r <- freshRel
        p <- dispatch c0 r
        pr <- dispatch (Prod c0 c1) (pairwise r q)
        clause (pairwise p r) pr
        pure p
    Sum c0 c1 -> do
      p <- freshRel
      p0 <- dispatch c0 q
      p1 <- dispatch c1 q
      clause p p0
      clause p p1
      pure p
    Loop c -> do
      p <- freshRel
      r <- dispatch c p
      clause r p
      clause p q
      pure p
    Prod c0 c1 ->
      if loopless c0 || loopless c1
      then do
        p <- freshRel
        q0 <- freshRel
        q1 <- freshRel
        p0 <- dispatch c0 q0
        p1 <- dispatch c1 q1
        -- TODO these clauses are not precise.
        clause (mkAnd q0 q1) q
        clause p p0
        clause p p1
        pure p
      else
        case mergeLoops c1 of
          Sum c1' c1'' -> dispatch (Sum (Prod c0 c1') (Prod c0 c1'')) q
          Prod c1' c1'' -> dispatch (Prod (Prod c0 c1') c1'') (associate q)
          Loop c1' -> dispatch (Prod (Loop c1') c0) (commute q)
          _ -> error ("Some impossible state has been reached: `" ++ show c ++ "`.")
