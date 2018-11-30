{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiWayIf #-}
module Self where

import Control.Monad.State
import Control.Monad.Writer hiding (Sum)
import Control.Monad.Except
import qualified Data.Set as S
import           Data.Set (Set)


import Debug.Trace

type Var = String

-- | The space of arithmetic expressions.
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

psubst :: Var -> Expr -> Prop -> Prop
psubst x e = \case
  T -> T
  F -> F
  Not p -> Not (go p)
  And p0 p1 -> And (go p0) (go p1)
  Impl p0 p1 -> Impl (go p0) (go p1)
  Eql e0 e1 -> Eql (goe e0) (goe e1)
  Lt e0 e1 -> Lt (goe e0) (goe e1)
  Ge e0 e1 -> Ge (goe e0) (goe e1)
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
  Lt e0 e1 -> Lt (goe e0) (goe e1)
  Ge e0 e1 -> Ge (goe e0) (goe e1)
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
  Lt e0 e1 -> S.union (evocab e0) (evocab e1)
  Ge e0 e1 -> S.union (evocab e0) (evocab e1)
  Rel _ es -> S.unions (map evocab es)

propRels :: Prop -> Set (ID, Int)
propRels = \case
  T -> S.empty
  F -> S.empty
  Not p -> propRels p
  And p0 p1 -> propRels p0 `S.union` propRels p1
  Impl p0 p1 -> propRels p0 `S.union` propRels p1
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

-- | A simple binary tree.
data Tree a
  = Leaf a
  | Branch (Tree a) (Tree a)
  deriving (Functor, Show, Read, Eq, Ord)

-- | Zip two trees with the same shape.
zipTree :: (a -> b -> c) -> Tree a -> Tree b -> Tree c
zipTree f (Leaf a) (Leaf b) = Leaf (f a b)
zipTree f (Branch a b) (Branch c d) = Branch (zipTree f a c) (zipTree f b d)

-- | A `vocabulary' consists of a tree where each leaf is a set of variables.
-- Once instantiated, the different leaves will be renamed with different
-- indices.
type Vocab = Tree (Set Var)

-- | Zip the vocab trees.
vocabUnion :: Vocab -> Vocab -> Vocab
vocabUnion = zipTree S.union

cvocab :: Com -> Vocab
cvocab = \case
  Assign x e -> Leaf (S.insert x (evocab e))
  Assert p -> Leaf (pvocab p)
  Skip -> Leaf S.empty
  Seq c0 c1 -> vocabUnion (cvocab c0) (cvocab c1)
  Sum c0 c1 -> vocabUnion (cvocab c0) (cvocab c1)
  Prod c0 c1 -> Branch (cvocab c0) (cvocab c1)
  Loop c -> cvocab c

-- | To implement program assertions, we need a consistent method for renaming
-- the variables in the assertions to some concrete, distinct values.
-- A VarChange is a tree which can apply different variable transformations to
-- different parts of assertions.
type VarChange = Tree (Var -> Var)

-- | Given some tree shape, builds a VarChange which renames variables by
-- adding an index based on the position in the tree where the variable
-- appears.
mkVarChange :: Tree a -> VarChange
mkVarChange s = evalState (go s) 0
  where
    go :: Tree a -> State Int VarChange
    go = \case
      Leaf _ -> do
        c <- get
        put (c+1)
        pure $ Leaf (\n -> n ++ "_" ++ show c)
      Branch s0 s1 -> Branch <$> go s0 <*> go s1

-- | An assertion can be thought of as a smart constructor for a Proposition.
-- The key difference is that an assertion can be over multiple program states
-- simultaneously. To distinguish the different program states, we use a
-- VarChange to rename the various variables appropriately.
-- In addition, an assertion carries a Vocabulary with live variables.
data Assertion = Assertion
  { vocab :: Vocab
  , fact :: VarChange -> Prop
  }

-- | Instiate the assertion by applying a VarChange based on the assertion
-- vocabulary.
instantiate :: Assertion -> Prop
instantiate (Assertion v phi) = phi (mkVarChange v)

-- | Commute the assertion: That is, swap how the assertion is applied to the
-- VarChange.
commute :: Assertion -> Assertion
commute (Assertion (Branch s0 s1) phi) =
  Assertion (Branch s1 s0)
            (\case
                Branch r0 r1 -> phi (Branch r1 r0)
                _ -> undefined)
commute _ = undefined

-- | Associate the assertion: That is, rotate how the assertion is applied to the
-- VarChange.
associateL :: Assertion -> Assertion
associateL (Assertion (Branch s0 (Branch s1 s2)) phi) =
  Assertion (Branch (Branch s0 s1) s2)
            (\case
                Branch (Branch r0 r1) r2 -> phi (Branch r0 (Branch r1 r2))
                _ -> undefined)
associateL _ = undefined

associateR :: Assertion -> Assertion
associateR (Assertion (Branch (Branch s0 s1) s2) phi) =
  Assertion (Branch s0 (Branch s1 s2))
            (\case
                Branch r0 (Branch r1 r2) -> phi (Branch (Branch r0 r1) r2)
                _ -> undefined)
associateR _ = undefined

pand :: Prop -> Prop -> Prop
pand T p = p
pand p T = p
pand F _ = F
pand _ F = F
pand p q = p `And` q

mkAnd :: Assertion -> Assertion -> Assertion
mkAnd (Assertion s0 phi0) (Assertion s1 phi1) =
  Assertion (vocabUnion s0 s1) (\r -> phi0 r `pand` phi1 r)

mkImpl :: Assertion -> Assertion -> Assertion
mkImpl (Assertion s0 phi0) (Assertion s1 phi1) =
  Assertion (vocabUnion s0 s1) (\r -> phi0 r `Impl` phi1 r)

pairwise :: Assertion -> Assertion -> Assertion
pairwise (Assertion s0 phi0) (Assertion s1 phi1) =
  Assertion (Branch s0 s1)
            (\case
              Branch r0 r1 -> pand (phi0 r0) (phi1 r1)
              _ -> undefined)

type M a = StateT Int (Writer [QProp]) a

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

data QProp = Forall [Var] Prop
  deriving (Show, Read, Eq, Ord)

quantify :: Prop -> QProp
quantify p = Forall (S.toList (pvocab p)) p

clause :: Assertion -> Assertion -> M ()
clause a0 a1 =
  let p = instantiate $ mkImpl a0 a1
      ps = split p
  in tell (map quantify ps)
   where
     split :: Prop -> [Prop]
     split (Impl p (And q r)) = split (Impl p q) ++ split (Impl p r)
     split p = [p]

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
dispatch c q = do
  traceM (showCom $ mergeLoops c)
  traceM ""
  case mergeLoops c of
    Assign x e ->
      pure (addVar x (subst x e q))
    Assert e -> do
      p <- freshRel (Leaf (pvocab e) `vocabUnion` vocab q)
      clause (andE p e) q
      pure p
    Skip -> pure q
    Seq c0 c1 ->
      if loopless c0 || loopless c1
      then dispatch c0 =<< dispatch c1 q
      else do
        r <- freshRel (cvocab c1 `vocabUnion` vocab q)
        p <- dispatch c0 r
        pr <- dispatch (Prod c0 c1) (pairwise r q)
        clause (pairwise p r) pr
        pure p
    Sum c0 c1 -> do
      p <- freshRel (cvocab c `vocabUnion` vocab q)
      p0 <- dispatch c0 q
      p1 <- dispatch c1 q
      clause p p0
      clause p p1
      pure p
    Loop c -> do
      p <- freshRel (cvocab c `vocabUnion` vocab q)
      r <- dispatch c p
      clause p r
      clause p q
      pure p
    Prod c0 c1 ->
      if loopless c0 || loopless c1
      then do
        let Branch v0 v1 = vocab q `vocabUnion` cvocab c
        p <- freshRel (Branch v0 v1)
        q0 <- freshRel v0
        q1 <- freshRel v1
        p0 <- dispatch c0 q0
        p1 <- dispatch c1 q1
        clause (pairwise q0 q1) q
        clause p (pairwise p0 p1)
        pure p
      else
        case c1 of
          Sum c1' c1'' -> dispatch (Sum (Prod c0 c1') (Prod c0 c1'')) q
          Prod c1' c1'' -> associateR <$> dispatch (Prod (Prod c0 c1') c1'') (associateL q)
          Loop c1' -> commute <$> dispatch (Prod (Loop c1') c0) (commute q)
          Seq c1' c1'' ->
            if loopless c1'
            then dispatch (Seq (Prod Skip c1') (Prod c0 c1'')) q
            else dispatch (Seq (Prod c0 c1') (Prod Skip c1'')) q
          _ -> error ("Some impossible state has been reached: `" ++ showCom c ++ "`.")

hoare :: Com -> [QProp]
hoare c =
  let (p, ps) = runWriter $ evalStateT (dispatch c (mkAssertion F)) 0
   in quantify (instantiate p) : (reverse ps)

example :: Com
example =
  Assign "x" (ALit 0) `Seq`
  Assign "x" (Add (ALit 1) (V "x")) `Seq`
  Assert (Not (Eql (V "x") (ALit 1)))

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
  Assert (Not (
    Impl
      (Eql (V "i0") (V "i1"))
      (Eql (V "s0") (V "s1"))))

example4 :: Com
example4 =
  Assign "a" (ALit 0) `Seq`
  Assign "b" (ALit 0) `Seq`
  Loop (
    Assert (Lt (V "b") (V "n")) `Seq`
    Assign "b" (Add (V "b") (ALit 1)) `Seq`
    Assign "a" (Add (V "a") (V "b"))
  ) `Seq`
  Assert (Not (Lt (V "b") (V "n"))) `Seq`
  Assert (Not (Ge (V "a") (V "n")))

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
    qrels (Forall _ p) = propRels p

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
