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

data CtxtNode a
  = L (Tree a)
  | R (Tree a)
  deriving (Functor, Show, Read, Eq, Ord)

type Ctxt a = [CtxtNode a]

contextualize :: Ctxt a -> Tree a -> Tree a
contextualize [] t = t
contextualize (L x:ctx) t = Branch x (contextualize ctx t)
contextualize (R x:ctx) t = Branch (contextualize ctx t) x

-- | Zip two trees with the same shape.
zipTree :: (a -> b -> c) -> Tree a -> Tree b -> Tree c
zipTree f (Leaf a) (Leaf b) = Leaf (f a b)
zipTree f (Branch a b) (Branch c d) = Branch (zipTree f a c) (zipTree f b d)

-- | A `vocabulary' consists of a tree where each leaf is a set of variables.
-- Once instantiated, the different leaves will be renamed with different
-- indices.
type Vocab = Tree (Set Var)
type VocabCtxt = Ctxt (Set Var)

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
type VarChangeCtxt = Ctxt (Var -> Var)

-- | Given some tree shape, builds a VarChange which renames variables by
-- adding an index based on the position in the tree where the variable
-- appears.
mkVarChange :: (Tree a, Ctxt a) -> (VarChange, VarChangeCtxt)
mkVarChange (t, c) = evalState ((,) <$> tree t <*> ctxt c) 0
  where
    ctxt = \case
      [] -> pure []
      (L x:cs) -> (:) <$> (L <$> tree x) <*> ctxt cs
      (R x:cs) -> (:) <$> (R <$> tree x) <*> ctxt cs

    tree :: Tree a -> State Int VarChange
    tree = \case
      Leaf _ -> do
        c <- get
        put (c+1)
        pure $ Leaf (\n -> n ++ "_" ++ show c)
      Branch s0 s1 -> Branch <$> tree s0 <*> tree s1

-- | An assertion can be thought of as a smart constructor for a Proposition.
-- The key difference is that an assertion can be over multiple program states
-- simultaneously. To distinguish the different program states, we use a
-- VarChange to rename the various variables appropriately.
-- In addition, an assertion carries a Vocabulary with live variables.

type Fact = VarChangeCtxt -> VarChange -> Prop

data Assertion = Assertion
  { ctxt :: VocabCtxt
  , vocab :: Vocab
  , fact :: Fact
  }

-- | Instiate the assertion by applying a VarChange based on the assertion
-- vocabulary.
instantiate :: Assertion -> Prop
instantiate (Assertion ctx v phi) = uncurry (flip phi) (mkVarChange (v, ctx))

-- | Commute the assertion: That is, swap how the assertion is applied to the
-- VarChange.
commute :: Assertion -> Assertion
commute (Assertion ctx (Branch s0 s1) phi) =
  Assertion ctx (Branch s1 s0)
            (\vctx r -> case r of
                Branch r0 r1 -> phi vctx (Branch r1 r0)
                _ -> undefined)
commute _ = undefined

-- | Associate the assertion: That is, rotate how the assertion is applied to the
-- VarChange.
associateL :: Assertion -> Assertion
associateL (Assertion ctx (Branch s0 (Branch s1 s2)) phi) =
  Assertion ctx (Branch (Branch s0 s1) s2)
            (\vctx r -> case r of
                Branch (Branch r0 r1) r2 -> phi vctx (Branch r0 (Branch r1 r2))
                _ -> undefined)
associateL _ = undefined

associateR :: Assertion -> Assertion
associateR (Assertion ctx ((Branch (Branch s0 s1) s2)) phi) =
  Assertion ctx (Branch s0 (Branch s1 s2))
            (\vctx r -> case r of
               Branch r0 (Branch r1 r2) -> phi vctx (Branch (Branch r0 r1) r2)
               _ -> undefined)
associateR _ = undefined

pand :: Prop -> Prop -> Prop
pand T p = p
pand p T = p
pand F _ = F
pand _ F = F
pand p q = p `And` q

mkImpl :: Assertion -> Assertion -> Assertion
mkImpl (Assertion ctx0 s0 phi0) (Assertion _ s1 phi1) =
  Assertion ctx0 (vocabUnion s0 s1) (\vctx r -> phi0 vctx r `Impl` phi1 vctx r)

pairwise :: Assertion -> Assertion -> Assertion
pairwise (Assertion ctx0 s0 phi0) (Assertion ctx1 s1 phi1) =
  Assertion (ctx0 ++ ctx1) (Branch s0 s1)
            (\vctx r -> case r of
              Branch r0 r1 ->
                pand (phi0 (if ctx0 == [] then [] else vctx) r0)
                     (phi1 (if ctx1 == [] then [] else vctx) r1)
              _ -> undefined)

left :: Assertion -> Assertion
left (Assertion ctx (Branch v0 v1) phi) =
  Assertion (L v0 : ctx) v1 (\ctx r ->
    case ctx of
      (L r0 : vctx) -> phi vctx (Branch r0 r)
      _ -> undefined)
left _ = undefined

unleft :: Assertion -> Assertion
unleft (Assertion (L ctx0:ctx) v phi) =
  Assertion ctx (Branch ctx0 v) (\ctx r ->
    case r of
      Branch r0 r1 -> phi (L r0 : ctx) r1
      _ -> undefined)
unleft _ = undefined

right :: Assertion -> Assertion
right (Assertion ctx (Branch v0 v1) phi) =
  Assertion (R v1 : ctx) v0 (\ctx r ->
    case ctx of
      (R r1 : vctx) -> phi vctx (Branch r r1)
      _ -> undefined)
right _ = undefined

unright :: Assertion -> Assertion
unright (Assertion (R ctx0:ctx) v phi) =
  Assertion ctx (Branch v ctx0) (\ctx r ->
    case r of
      Branch r0 r1 -> phi (R r1 : ctx) r0
      _ -> undefined)
unright _ = undefined

type M a = StateT Int (Writer [QProp]) a

freshRel :: VocabCtxt -> Vocab -> M Assertion
freshRel ctx v = do
  let v' = contextualize ctx v
  c <- get
  put (c+1)
  pure (Assertion ctx v (\vctx r -> Rel c (relVocab v' (contextualize vctx r))))
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
mkAssertion p = Assertion [] (Leaf $ pvocab p) (\_ r -> case r of
  Leaf r -> prename r p
  _ -> undefined)

andE :: Assertion -> Prop -> Assertion
andE (Assertion ctx v phi) p =
  Assertion ctx (vocabUnion v (Leaf $ pvocab p)) (\vctx r -> case r of
    Leaf r -> prename r p `pand` phi vctx (Leaf r)
    _ -> undefined)

subst :: Var -> Expr -> Assertion -> Assertion
subst x e (Assertion ctx v phi) =
  Assertion ctx v (\vctx r -> case r of
    Leaf r -> psubst (r x) (erename r e) (phi vctx (Leaf r))
    _ -> undefined)

addVar :: Var -> Assertion -> Assertion
addVar x (Assertion ctx (Leaf v) phi) =
  Assertion ctx (Leaf (S.insert x v)) phi

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
      p <- freshRel (ctxt q) (Leaf (pvocab e) `vocabUnion` vocab q)
      clause (andE p e) q
      pure p
    Skip -> pure q
    Seq c0 c1 ->
      if loopless c0 || loopless c1
      then dispatch c0 =<< dispatch c1 q
      else do
        r <- freshRel (ctxt q) (cvocab c `vocabUnion` vocab q)
        p <- dispatch c0 r
        pr <- dispatch (Prod c0 c1) (pairwise r q)
        clause (pairwise p r) pr
        pure p
    Sum c0 c1 -> do
      p <- freshRel (ctxt q) (cvocab c `vocabUnion` vocab q)
      p0 <- dispatch c0 q
      p1 <- dispatch c1 q
      clause p p0
      clause p p1
      pure p
    Loop c -> do
      p <- freshRel (ctxt q) (cvocab c `vocabUnion` vocab q)
      r <- dispatch c p
      clause p r
      clause p q
      pure p
    Prod c0 c1 ->
      if loopless c0 || loopless c1
      then do
        r <- unleft <$> dispatch c1 (left q)
        unright <$> dispatch c0 (right r)
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
