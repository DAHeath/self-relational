{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE FlexibleContexts #-}
module Self where

import Control.Monad.State
import Control.Monad.Writer hiding (Sum)
import Control.Monad.Reader
import qualified Data.Set as S
import           Data.Set (Set)
import qualified Data.Map as M
import           Data.Map (Map)
import           Data.List (intercalate, nub)

import Debug.Trace

-- | We just use strings as the space of variables.
type Var = String

-- | The space of arithmetic expressions.
data Expr
  = ALit Integer
  | Add Expr Expr
  | V Var
  deriving (Show, Read, Eq, Ord)

-- | We name logical relations using integer identifiers.
type ID = Int

-- | The space of (quantifier-free) logical propositions.
data Prop
  -- We include standard logical combinators...
  = T
  | F
  | Not Prop
  | And Prop Prop
  | Or Prop Prop
  | Impl Prop Prop
  -- And we include propositions over expressions.
  | Eql Expr Expr
  | Lt Expr Expr
  | Ge Expr Expr
  | Rel ID [Expr]
  deriving (Show, Read, Eq, Ord)

-- An implementation of logical AND that constant folds.
(/\) :: Prop -> Prop -> Prop
(/\) T p = p
(/\) p T = p
(/\) F _ = F
(/\) _ F = F
(/\) p q = p `And` q

-- An implementation of logical OR that constant folds.
(\/) :: Prop -> Prop -> Prop
(\/) T _ = T
(\/) _ T = T
(\/) F p = p
(\/) p F = p
(\/) p q = p `Or` q

esubst :: Int -> Map Var Expr -> Expr -> Expr
esubst i m = \case
  ALit n -> ALit n
  V v ->
    let v' = v ++ "_" ++ show i
    in M.findWithDefault (V v') v m
  Add a0 a1 -> Add (esubst i m a0) (esubst i m a1)

esimp :: Expr -> Expr
esimp (Add (ALit i) (ALit j)) = ALit (i + j)
esimp (Add e0 e1) = Add (esimp e0) (esimp e1)
esimp e = e

psubst :: Int -> Map Var Expr -> Prop -> Prop
psubst i m = \case
  T -> T
  F -> F
  Not p -> Not (go p)
  And p0 p1 -> And (go p0) (go p1)
  Or p0 p1 -> Or (go p0) (go p1)
  Impl p0 p1 -> Impl (go p0) (go p1)
  Eql e0 e1 -> Eql (goe e0) (goe e1)
  Lt e0 e1 -> Lt (goe e0) (goe e1)
  Ge e0 e1 -> Ge (goe e0) (goe e1)
  where
    go = psubst i m
    goe = esubst i m

psimp :: Prop -> Prop
psimp p =
  let q = go p
   in if p == q then q
                else psimp q
  where
    go T = T
    go F = F
    go (Not (Not p)) = p
    go (Not p) = Not (go p)
    go (And p q) = (/\) (go p) (go q)
    go (Or p q) = (\/) (go p) (go q)
    go (Impl T p) = p
    go (Impl p q) = Impl (go p) (go q)
    go (Eql e0 e1) =
      let e0' = esimp e0
          e1' = esimp e1
      in if e0' == e1' then T
                       else Eql e0' e1'
    go (Lt e0 e1) = Lt (esimp e0) (esimp e1)
    go (Ge e0 e1) = Ge (esimp e0) (esimp e1)
    go (Rel i es) = Rel i (map esimp es)

-- | The vocabulary of an expression.
evocab :: Expr -> Set Var
evocab = \case
  V v -> S.singleton v
  Add e0 e1 -> S.union (evocab e0) (evocab e1)
  ALit{} -> S.empty

-- | The vocabulary of a proposition.
pvocab :: Prop -> Set Var
pvocab = \case
  T -> S.empty
  F -> S.empty
  Not p -> pvocab p
  And p0 p1 -> S.union (pvocab p0) (pvocab p1)
  Or p0 p1 -> S.union (pvocab p0) (pvocab p1)
  Impl p0 p1 -> S.union (pvocab p0) (pvocab p1)
  Eql e0 e1 -> S.union (evocab e0) (evocab e1)
  Lt e0 e1 -> S.union (evocab e0) (evocab e1)
  Ge e0 e1 -> S.union (evocab e0) (evocab e1)
  Rel _ es -> S.unions (map evocab es)

-- | The set of logical relations named in the proposition (together with the
-- number of arguments to each relation).
propRels :: Prop -> Set (ID, Int)
propRels = \case
  T -> S.empty
  F -> S.empty
  Not p -> propRels p
  And p0 p1 -> propRels p0 `S.union` propRels p1
  Or p0 p1 -> propRels p0 `S.union` propRels p1
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

-- | The vocabulary of a command.
cvocab :: Com -> Set Var
cvocab = \case
  Assign v e -> S.insert v $ evocab e
  Assert p -> pvocab p
  Skip -> S.empty
  Seq c0 c1 -> cvocab c0 `S.union` cvocab c1
  Sum c0 c1 -> cvocab c0 `S.union` cvocab c1
  Prod c0 c1 -> cvocab c0 `S.union` cvocab c1
  Loop c -> cvocab c

-- | Does the command contain no loops?
loopless :: Com -> Bool
loopless = \case
  Loop{} -> False
  Sum c0 c1 -> loopless c0 && loopless c1
  Prod c0 c1 -> loopless c0 && loopless c1
  Seq c0 c1 -> loopless c0 && loopless c1
  Assert{} -> True
  Assign{} -> True
  Skip -> True

-- | Is the first command in a sequence not a loop.
looplessStart :: Com -> Bool
looplessStart = \case
  Seq c0 _ -> looplessStart c0
  c -> loopless c

-- | Is the lsast command in a sequence not a loop.
looplessEnd :: Com -> Bool
looplessEnd = \case
  Seq _ c1 -> looplessEnd c1
  c -> loopless c

-- | The space of program states. A state is either a map from variables to the
-- counter used as a temporary over that variable, or it is a product of two
-- states.
data St = Singleton Int (Map Var Expr) | Composite St St
  deriving (Show, Read, Eq, Ord)

-- | The context used to construct fresh variables. We include a counter for
-- fresh logical relations and a counter for fresh variables.
data Ctxt = Ctxt
  { relCount :: Int
  , varCount :: Int
  , iState :: St
  } deriving (Show, Read, Eq, Ord)

-- | A proposition quantified over a vocabulary.
data QProp = Forall [Var] Prop
  deriving (Show, Read, Eq, Ord)

-- | The monadic effect used to compute the constraints.
-- First, the output of the computation is a set of constraints. The
-- constraints are represented by quantified propositions. These are written
-- out using Writer.
-- A context is maintained to track which variable/relation names are fresh.
-- An environment is maintained to properly instantiate logical relations with
-- the correct vocabulary.
type M a = ReaderT (St -> St) (StateT Ctxt (Writer [QProp])) a

fresh :: St -> M St
fresh (Composite st0 st1) = Composite <$> fresh st0 <*> fresh st1
fresh (Singleton _ m) = do
  c <- state (\ctx -> (varCount ctx, ctx { varCount = varCount ctx + 1 }))
  pure (Singleton c (M.mapWithKey (\k _ -> V (k ++ "_" ++ show c)) m))

-- | The core operation of this library. Given a command, a precondition, and a
-- program state (that the precondition is over) the operation computes a
-- postcondition and a new program state (that the postcondition is over).
-- It does this by applying the proof rules for self-relational Hoare logic.
triple :: Com -> Prop -> St -> M (Prop, St)
triple c p st = case c of
  -- Skip has no effect.
  Skip -> pure (p, st)
  -- Assign generates a fresh variable and sets this fresh variable equal to
  -- the expression.
  Assign x a -> do
    let Singleton i m = st
    let a' = esubst i m a
    let m' = M.insert x a' m
    pure (p, Singleton i m')
  -- The effect of an assertion is summarized by the asserted proposition
  -- itself (over the correct vocabulary).
  Assert e -> do
    let Singleton i m = st
    pure (p /\ psubst i m e, st)
  -- If the command is a sequence, there are still possibilities for
  -- optimizations despite there being at least one loop.
  Seq c0 c1 ->
    if | loopless c0 || loopless c1 -> do
          (r, st') <- triple c0 p st
          triple c1 r st'
       | looplessStart c0 ->
        -- If there is a loopless start, we can attempt to chop the start off now.
          case c0 of
            -- If the first command is a sequence, then reassociate to move
            -- towards the beginning of the sequence.
            Seq c0' c0'' -> triple (Seq c0' (Seq c0'' c1)) p st
            -- Otherwise, dispatch that first command now (since we know it is not a loop).
            c -> do
              (q, st') <- triple c0 p st
              (r, st'') <- triple c1 q st'
              pure (r, st'')
       | looplessEnd c1 ->
        -- If there is a loopless end, we can attempt to chop the end off now.
          case c1 of
            -- If the second command is a sequence, then reassociate to move
            -- towards the end of the sequence.
            Seq c1' c1'' -> triple (Seq (Seq c0 c1') c1'') p st
            -- Otherwise, dispatch that second command now (since we know it is not a loop).
            c -> do
              (q, st') <- triple c0 p st
              (r, st'') <- triple c1 q st'
              pure (r, st'')
       | otherwise -> do
         -- If (1) the sequence contains a loop, (2) the beginning of the
         -- sequence is a loop, and (3) the end of the sequence is a loop
         -- then we are in the general case: Both commands in the sequence
         -- must be considered simultaneously. Apply the seq/prod rule to
         -- reason about both parts of the sequence together.
         st1 <- fresh st
         (q, st') <- triple (Prod Skip c0) (p /\ equiv st st1) (Composite st st1)
         (r, st'') <- triple (Prod c0 c1) q st'
         (s, Composite st0' st1') <- triple (Prod c1 Skip) r st''
         pure (s /\ equiv st0' st1', st0')
  -- If the command is a sum, we must reason over the two summands separately.
  Sum c0 c1 -> do
    (q0, st0) <- triple c0 p st
    (q1, st1) <- triple c1 p st
    r <- rel
    q0 ==> r st0
    q1 ==> r st1
    st' <- fresh st0
    pure (r st', st')
  -- To handle loops, we apply the loop rule (by constructing a fresh
  -- relational predicate to represent the loop invariant).
  Loop c -> do
    r <- rel
    p ==> r st
    st0 <- fresh st
    (q, st') <- triple c (r st0) st0
    -- Each loop introduces two new constraints (by applying the consequence
    -- rule). One states that the precondition implies the loop invariant
    -- (over the pre-state) and the second states that the body maintains the
    -- loop invariant.
    q ==> r st'
    -- The post-condition of the loop is the loop invariant.
    pure (r st0, st0)
  -- Several optimizations are possible in the case of products.
  Prod c0 c1 ->
    -- If either multiplicand has no loops, it is sufficient to reason about
    -- them separately.
    if loopless c0 || loopless c1
    then do
      let Composite st0 st1 = st
      -- Note that we must add state to the environment: Propositions for
      -- one command are allowed to refer to the vocabulary of its peer.
      (q0, st0') <- local (. (`Composite` st1)) (triple c0 p st0)
      (q1, st1') <- local (. (st0' `Composite`)) (triple c1 q0 st1)
      pure (q1, Composite st0' st1')
    -- If both multiplicands have loops, then we will apply isomorphisms to
    -- group loops together.  Eventually the loop/product isomorphism will
    -- merge loops.
    else triple (rewrite c0 c1) p st

rewrite :: Com -> Com -> Com
rewrite (Loop c0) (Loop c1) = Loop (Prod c0 c1)
rewrite (Loop c) Skip = Loop (Prod c Skip)
rewrite Skip (Loop c) = Loop (Prod Skip c)
rewrite c0 (Sum c1 c2) = Sum (Prod c0 c1) (Prod c0 c2)
rewrite (Sum c0 c1) c2 = Sum (Prod c0 c2) (Prod c1 c2)
rewrite c0 (Prod c1 c2) = Prod c0 (rewrite c1 c2)
rewrite (Prod c0 c1) c2 = Prod (rewrite c0 c1) c2
rewrite c0 (Seq c1 c2)
  | loopless c1 = Seq (Prod Skip c1) (Prod c0 c2)
  | otherwise = Seq (Prod c0 c1) (Prod Skip c2)
rewrite (Seq c0 c1) c2
  | loopless c0 = Seq (Prod c0 Skip) (Prod c1 c2)
  | otherwise = Seq (Prod c0 c2) (Prod c1 Skip)
rewrite (Loop c0) c1 = rewrite (Loop c0) (Seq c1 Skip)
rewrite c0 (Loop c1) = rewrite (Seq c0 Skip) (Loop c1)
rewrite c0 c1 = Prod c0 c1

-- Given a command, construct a set of constraints that model the command.
--
-- This is implemented by simply making a call to `triple` with appropriate
-- arguments and in an appropriate environment.
hoare :: Com -> [QProp]
hoare c =
  let voc = S.toList $ cvocab c
      initialState = Singleton 0 (M.fromList (zip voc (map (\v -> V (v ++ "_0")) voc)))
      ctx = Ctxt
        { relCount = 0
        , varCount = 1
        , iState = initialState
        }
   in execWriter $ evalStateT (runReaderT
        (do
          (q, _) <- triple c T initialState
          q ==> F) id) ctx

rel :: M (St -> Prop)
rel = do
  c <- state (\ctx -> (relCount ctx, ctx { relCount = relCount ctx + 1 }))
  fSt <- ask
  pure (Rel c . collapse . fSt)
  where
    collapse :: St -> [Expr]
    collapse (Composite st0 st1) = collapse st0 ++ collapse st1
    collapse (Singleton _ m) = M.elems m

quantify :: Prop -> QProp
quantify p = Forall (S.toList (pvocab p)) p

(==>) :: Prop -> Prop -> M ()
(==>) p q = tell [quantify (psimp (p `Impl` q))]

equiv :: St -> St -> Prop
equiv (Composite st0 st1) (Composite st0' st1') = equiv st0 st0' /\ equiv st1 st1'
equiv (Singleton _ m0) (Singleton _ m1) =
  let vs = S.fromList (M.keys m0) `S.union` S.fromList (M.keys m1)
      fetch v = M.findWithDefault (V v) v
   in foldr (/\) T (map (\v -> fetch v m0 `Eql` fetch v m1) (S.toList vs))

showCom :: Com -> String
showCom = \case
  Skip -> "skip"
  Assign v e -> v ++ " := " ++ smt2Expr e
  Assert e -> "assert " ++ smt2Prop e
  Seq c0 c1 -> showCom c0 ++ ";\n" ++ showCom c1
  Sum c0 c1 -> "{" ++ showCom c0 ++ "} +\n {" ++ showCom c1 ++ "}"
  Prod c0 c1 -> "{" ++ showCom c0 ++ "} *\n {" ++ showCom c1 ++ "}"
  Loop c -> "Loop {" ++ showCom c ++ "}"

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
  And p0 p1 -> sexpr ("and" : map smt2Prop (nub $ conjuncts p0 ++ conjuncts p1))
  Or p0 p1 -> sexpr ("or" : map smt2Prop (nub $ disjuncts p0 ++ disjuncts p1))
  Impl p0 p1 -> sexpr ["=>", smt2Prop p0, smt2Prop p1]
  Eql e0 e1 -> sexpr ["=", smt2Expr e0, smt2Expr e1]
  Lt e0 e1 -> sexpr ["<", smt2Expr e0, smt2Expr e1]
  Ge e0 e1 -> sexpr [">=", smt2Expr e0, smt2Expr e1]
  Rel i es -> sexpr (("R" ++ show i) : map smt2Expr es)
  where
    conjuncts :: Prop -> [Prop]
    conjuncts (And p0 p1) = conjuncts p0 ++ conjuncts p1
    conjuncts p = [p]
    disjuncts :: Prop -> [Prop]
    disjuncts (Or p0 p1) = disjuncts p0 ++ disjuncts p1
    disjuncts p = [p]

example :: Com
example =
  Assign "x" (ALit 0) `Seq`
  Assign "x" (Add (V "x") (ALit 1)) `Seq`
  -- Assign "x" (Add (V "x") (ALit 1)) `Seq`
  Assert (Not (Eql (V "x") (ALit 1)))

loopCopy :: Com
loopCopy =
  Assign "s0" (ALit 0) `Seq`
  Assign "s1" (ALit 0) `Seq`
  Assign "i" (ALit 0) `Seq`
  Loop (Sum ( Assert (Lt (V "i") (V "n")) `Seq`
              Assign "s0" (Add (V "s0") (V "i")) `Seq`
              Assign "i" (Add (V "i") (ALit 1))
            ) (Assert (Ge (V "i") (V "n")))
    ) `Seq`
  Assert (Ge (V "i") (V "n")) `Seq`
  Assign "i" (ALit 0) `Seq`
  Loop (Sum ( Assert (Lt (V "i") (V "n")) `Seq`
              Assign "s1" (Add (V "s1") (V "i")) `Seq`
              Assign "i" (Add (V "i") (ALit 1))
            ) (Assert (Ge (V "i") (V "n")))
    ) `Seq`
  Assert (Ge (V "i") (V "n")) `Seq`
  Assert (Not (Eql (V "s0") (V "s1")))

loopFusion :: Com
loopFusion =
  Assign "s0" (ALit 0) `Seq`
  Assign "s1" (ALit 0) `Seq`
  Assign "i" (ALit 0) `Seq`
  Loop (Sum ( Assert (Lt (V "i") (V "n")) `Seq`
              Assign "s0" (Add (V "s0") (V "i")) `Seq`
              Assign "s1" (Add (V "s1") (V "i")) `Seq`
              Assign "i" (Add (V "i") (ALit 1))
            ) (Assert (Ge (V "i") (V "n")))
    ) `Seq`
    Assert (Ge (V "i") (V "n")) `Seq`

  Assign "i" (ALit 0) `Seq`
  Assign "s2" (ALit 0) `Seq`
  Loop (Sum ( Assert (Lt (V "i") (V "n")) `Seq`
              Assign "s2" (Add (V "s2") (V "i")) `Seq`
              Assign "i" (Add (V "i") (ALit 1))
            ) (Assert (Ge (V "i") (V "n")))
    ) `Seq`
    Assert (Ge (V "i") (V "n")) `Seq`

  Assign "i" (ALit 0) `Seq`
  Assign "s3" (ALit 0) `Seq`
  Loop (Sum ( Assert (Lt (V "i") (V "n")) `Seq`
              Assign "s3" (Add (V "s3") (V "i")) `Seq`
              Assign "i" (Add (V "i") (ALit 1))
            ) (Assert (Ge (V "i") (V "n")))
    ) `Seq`
    Assert (Ge (V "i") (V "n")) `Seq`

  Assert (Not (And (Eql (V "s0") (V "s2")) (Eql (V "s1") (V "s3"))))
