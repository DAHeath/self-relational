{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiWayIf #-}
module Self where

import Control.Monad.State
import Control.Monad.Writer hiding (Sum)
import Control.Monad.Except
import qualified Data.Set as S
import           Data.Set (Set)

type Var = String

data Expr
  = ALit Integer
  | Add Expr Expr
  | V Var
  deriving (Show, Read, Eq, Ord)

esubst :: Var -> Expr -> Expr -> Expr
esubst x e = \case
  ALit i -> ALit i
  Add e0 e1 -> Add (go e0) (go e1)
  V v -> if v == x then e else V v
  where
    go = esubst x e

erename :: (Var -> Var) -> Expr -> Expr
erename f = \case
  ALit i -> ALit i
  V v -> V (f v)
  Add a0 a1 -> Add (erename f a0) (erename f a1)

evocab :: Expr -> Set Var
evocab = \case
  V v -> S.singleton v
  Add e0 e1 -> S.union (evocab e0) (evocab e1)
  ALit{} -> S.empty

type ID = Int

data Prop
  = T
  | F
  | Not Prop
  | And Prop Prop
  | Impl Prop Prop
  | Eql Expr Expr
  | Rel ID [Expr]
  deriving (Show, Read, Eq, Ord)

psubst :: Var -> Expr -> Prop -> Prop
psubst x e = \case
  T -> T
  F -> F
  Not p -> Not (go p)
  And p0 p1 -> And (go p0) (go p1)
  Impl p0 p1 -> Impl (go p0) (go p1)
  Eql e0 e1 -> Eql (goe e0) (goe e1)
  Rel i es -> Rel i (map goe es)
  where
    go = psubst x e
    goe = esubst x e

prename :: (Var -> Var) -> Prop -> Prop
prename f= \case
  T -> T
  F -> F
  Not p -> Not (go p)
  And p0 p1 -> And (go p0) (go p1)
  Impl p0 p1 -> Impl (go p0) (go p1)
  Eql e0 e1 -> Eql (goe e0) (goe e1)
  where
    go = prename f
    goe = erename f

pvocab :: Prop -> Set Var
pvocab = \case
  T -> S.empty
  F -> S.empty
  Not p -> pvocab p
  And p0 p1 -> S.union (pvocab p0) (pvocab p1)
  Impl p0 p1 -> S.union (pvocab p0) (pvocab p1)
  Eql e0 e1 -> S.union (evocab e0) (evocab e1)
  Rel _ es -> S.unions (map evocab es)

data Com
  = Assign Var Expr
  | Assert Prop
  | Skip
  | Seq Com Com
  | Sum Com Com
  | Prod Com Com
  | Loop Com
  deriving (Show, Read, Eq, Ord)

data Tree a
  = Leaf a
  | Branch (Tree a) (Tree a)
  deriving (Functor, Show, Read, Eq, Ord)

zipTree :: (a -> b -> c) -> Tree a -> Tree b -> Tree c
zipTree f (Leaf a) (Leaf b) = Leaf (f a b)
zipTree f (Branch a b) (Branch c d) = Branch (zipTree f a c) (zipTree f b d)

type Vocab = Tree (Set Var)

vocabUnion :: Vocab -> Vocab -> Vocab
vocabUnion = zipTree S.union

type VarChange = Tree (Var -> Var)

mkVarChange :: Tree a -> VarChange
mkVarChange s = evalState (go s) 0
  where
    go :: Tree a -> State Int VarChange
    go = \case
      Leaf _ -> do
        c <- get
        put (c+1)
        pure $ Leaf (\n -> n ++ show c)
      Branch s0 s1 -> Branch <$> go s0 <*> go s1

instantiate :: Assertion -> Prop
instantiate (Assertion v phi) = phi (mkVarChange v)

data Assertion = Assertion
  { vocab :: Vocab
  , fact :: VarChange -> Prop
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
mkAnd (Assertion s0 phi0) (Assertion s1 phi1) =
  Assertion (vocabUnion s0 s1) (\r -> phi0 r `And` phi1 r)

mkImpl :: Assertion -> Assertion -> Assertion
mkImpl (Assertion s0 phi0) (Assertion s1 phi1) =
  Assertion (vocabUnion s0 s1) (\r -> phi0 r `Impl` phi1 r)

pairwise :: Assertion -> Assertion -> Assertion
pairwise (Assertion s0 phi0) (Assertion s1 phi1) =
  Assertion (Branch s0 s1)
            (\case
              Branch r0 r1 -> And (phi0 r0) (phi1 r1)
              _ -> undefined)

type M a = StateT Int (Writer [Prop]) a

freshRel :: Vocab -> M Assertion
freshRel v = do
  c <- get
  put (c+1)
  pure (Assertion v (\r -> Rel c (relVocab v r)))
  where
    relVocab :: Vocab -> VarChange -> [Expr]
    relVocab v r =
      case (v, r) of
        (Leaf v, Leaf r) -> map (V . r) (S.toList v)
        (Branch v0 v1, Branch r0 r1) -> relVocab v0 r0 ++ relVocab v1 r1
        _ -> undefined


clause :: Assertion -> Assertion -> M ()
clause a0 a1 =
  tell [instantiate $ mkImpl a0 a1]

mkAssertion :: Prop -> Assertion
mkAssertion p = Assertion (Leaf $ pvocab p) (\case
  Leaf r -> prename r p
  _ -> undefined)

andE :: Assertion -> Prop -> Assertion
andE a p = mkAnd a (mkAssertion p)

subst :: Var -> Expr -> Assertion -> Assertion
subst x e (Assertion v phi) =
  Assertion v (\case
    Leaf r -> psubst (r x) (erename r e) (phi (Leaf r))
    _ -> undefined)

addVar :: Var -> Assertion -> Assertion
addVar x (Assertion (Leaf v) phi) = Assertion (Leaf (S.insert x v)) phi

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
      pure (addVar x (subst x e q))
    Assert e -> do
      p <- freshRel (Leaf (pvocab e) `vocabUnion` vocab q)
      clause (andE p e) q
      pure p
    Skip -> pure q
    Seq c0 c1 ->
      if loopless c0 || loopless c1
      then do
        r <- dispatch c1 q
        dispatch c0 r
      else do
        r <- freshRel (vocab q)
        p <- dispatch c0 r
        pr <- dispatch (Prod c0 c1) (pairwise r q)
        clause (pairwise p r) pr
        pure p
    Sum c0 c1 -> do
      p <- freshRel (vocab q)
      p0 <- dispatch c0 q
      p1 <- dispatch c1 q
      clause p p0
      clause p p1
      pure p
    Loop c -> do
      p <- freshRel (vocab q)
      r <- dispatch c p
      clause r p
      clause p q
      pure p
    Prod c0 c1 ->
      if loopless c0 || loopless c1
      then do
        p <- freshRel (vocab q)
        q0 <- freshRel (vocab q)
        q1 <- freshRel (vocab q)
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

hoare :: Com -> [Prop]
hoare c =
  let (p, ps) = runWriter $ evalStateT (dispatch c (mkAssertion F)) 0
   in instantiate p : ps

example :: Com
example =
  Assign "x" (ALit 0) `Seq`
  Assign "x" (Add (ALit 1) (V "x")) `Seq`
  Assert (Not (Eql (V "x") (ALit 1)))


