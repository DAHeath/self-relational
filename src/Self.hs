{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
module Self where

import Control.Monad.State
import Control.Monad.Writer hiding (Sum)
import Control.Monad.Reader
import qualified Data.Set as S
import           Data.Set (Set)
import qualified Data.Map as M
import           Data.Map (Map)
import           Data.List (intercalate, nub)

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

-- | In order to support the proof rules, we will rename variables to fresh
-- temporary variables. To do so, we use a map from variable names to a counter
-- that indicates which temporary to use.
vrename :: Map Var Int -> Var -> Var
vrename m v = (v ++ "_" ++ show (M.findWithDefault 0 v m))

-- | Renaming for expressions. See `vrename`.
erename :: Map Var Int -> Expr -> Expr
erename m = \case
  ALit i -> ALit i
  V v -> V (vrename m v)
  Add a0 a1 -> Add (erename m a0) (erename m a1)

-- | Renaming for propositions. See `vrename`.
prename :: Map Var Int -> Prop -> Prop
prename m = \case
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
    go = prename m
    goe = erename m

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

-- | Apply the loop merge isomorphism:
-- LOOP { c0 } * LOOP { c1 } = LOOP { c0 * c1 }
--
-- Note that this isomorphism is not valid in full generality. It is valid here
-- because we ensure that all loops are properly constructed to be a
-- disjunction over a loop guard condition.
mergeLoops :: Com -> Com
mergeLoops = \case
  Prod c0 c1 ->
    let c0' = mergeLoops c0
        c1' = mergeLoops c1
    in case (c0', c1') of
         (Loop c0, Loop c1) -> Loop (c0 `Prod` c1)
         _ -> Prod c0' c1'
  c -> c

-- | The space of program states. A state is either a map from variables to the
-- counter used as a temporary over that variable, or it is a product of two
-- states.
data St = Singleton (Map Var Int) | Composite St St
  deriving (Show, Read, Eq, Ord)

-- | The context used to construct fresh variables. We include a counter for
-- fresh logical relations and a counter for fresh variables.
data Ctxt = Ctxt
  { relCount :: Int
  , varCount :: Int
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

-- | The core operation of this library. Given a command, a precondition, and a
-- program state (that the precondition is over) the operation computes a
-- postcondition and a new program state (that the postcondition is over).
-- It does this by applying the proof rules for self-relational Hoare logic.
triple :: Com -> Prop -> St -> M (Prop, St)
triple c p st
  -- As an optimization, if the command has no loops then it can be completely
  -- summarized by a single proposition without the need for relational
  -- predicates.
  | loopless c = do
    (q, st') <- summary c st
    pure (p /\ q, st')
  -- First, eagerly try to merge loops together using the loop/product isomorphism.
  | otherwise = case mergeLoops c of
    -- If the command is a sequence, there are still possibilities for
    -- optimizations despite there being at least one loop.
    Seq c0 c1 ->
      if | looplessStart c0 ->
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
          -- If there is a looplesend start, we can attempt to chop the end off now.
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
           (q, st') <- triple (Prod Skip c0) (p) (Composite st st)
           (r, st'') <- triple (Prod c0 c1) q st'
           (s, Composite st0 st1) <- triple (Prod c1 Skip) r st''
           pure (s /\ equiv st0 st1, st0)
    -- If the command is a sum, we must reason over the two summands separately.
    Sum c0 c1 -> do
      (q0, st0) <- triple c0 p st
      (q1, st1) <- triple c1 p st
      -- Note that each summand will generate a different output state. We must
      -- ensure that the output state of the overall command is consistent.
      -- `resolve` does this while providing any propositions of equality
      -- needed to achieve this resolution.
      let (st', r0, r1) = resolve st0 st1
      pure ((q0 /\ r0) \/ (q1 /\ r1), st')
    -- To handle loops, we just apply the loop rules (by constructing a fresh
    -- relational predicate to represent the loop invariant).
    Loop c -> do
      r <- rel
      (q, st') <- triple c (r st) st
      -- Each loop introduces two new constraints (by applying the consequence
      -- rule). One states that the precondition implies the loop invariant
      -- (over the pre-state) and the second states that the body maintains the
      -- loop invariant.
      p ==> r st
      q ==> r st'
      -- The post-condition of the loop is the loop invariant.
      pure (r st', st')
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
        (q1, st1') <- local (. (st0 `Composite`)) (triple c1 p st1)
        pure (q0 /\ q1, Composite st0' st1')
      -- If both multiplicands have loops, then we must rearrange the product
      -- to bring those loops together. The overall goal is to eventually allow
      -- `mergeLoops` to eliminate products of loops.
      else case c1 of
        -- If one of the multiplicands is a sum, distribute the sum over the product.
        Sum c1' c1'' -> triple (Sum (Prod c0 c1') (Prod c0 c1'')) p st
        -- If one of the multiplicands is itself a product, then reassociate.
        Prod c1' c1'' -> associate (triple (Prod (Prod c0 c1') c1'') p) st
        -- If one of the multiplicands is a loop, the commute so as to make
        -- progress on the other multiplicand.
        Loop c1' -> commute (triple (Prod (Loop c1') c0) p) st
        -- If one of the multiplicands is a sequence, we distribute the
        -- sequence over the product while trying to keep loops grouped.
        Seq c1' c1'' ->
          if loopless c1'
          then triple (Seq (Prod Skip c1') (Prod c0 c1'')) p st
          else triple (Seq (Prod c0 c1') (Prod Skip c1'')) p st
        _ -> error ("Some impossible state has been reached: `" ++ showCom c ++ "`.")

-- | When a command has no loops, we can fully summarize its effect with a single relational predicate.
summary :: Com -> St -> M (Prop, St)
summary c st = case c of
  -- Skip has no effect.
  Skip -> pure (T, st)
  -- Assign generates a fresh variable and sets this fresh variable equal to
  -- the expression.
  Assign x a -> do
    let Singleton m = st
    v <- state (\ctx -> (varCount ctx, ctx { varCount = varCount ctx + 1 }))
    let m' = M.insert x v m
    pure (Eql (erename m' (V x)) (erename m a), Singleton m')
  -- The effect of an assertion is summarized by the asserted proposition
  -- itself (over the correct vocabulary).
  Assert e -> do
    let Singleton m = st
    pure (prename m e, st)
  -- The sequence of two commands is summarized by conjoining the sub-summaries.
  Seq c0 c1 -> do
    (p, st') <- summary c0 st
    (q, st'') <- summary c1 st'
    pure (p /\ q, st'')
  -- The sum of two commands is summarized by disjoining the sub-summaries.
  Sum c0 c1 -> do
    (p0, st0) <- summary c0 st
    (p1, st1) <- summary c1 st
    -- Similar to `triple`, we must ensure that the vocabulary of the two
    -- output states are resolved into a single vocabulary.
    let (st', q0, q1) = resolve st0 st1
    pure ((p0 /\ q0) \/ (p1 /\ q1), st')
  -- The product of two commands is summarized by conjoining the sub-summaries
  -- and joining their output vocabularies.
  Prod c0 c1 -> do
    let Composite st0 st1 = st
    (p0, st0') <- summary c0 st0
    (p1, st1') <- summary c1 st1
    pure (p0 /\ p1, Composite st0' st1')

-- Given a command, construct a set of constraints that model the command.
--
-- This is implemented by simply making a call to `triple` with appropriate
-- arguments and in an appropriate environment.
hoare :: Com -> [QProp]
hoare c =
  let voc = S.toList $ cvocab c
      ctx = Ctxt
        { relCount = 0
        , varCount = length voc
        }
      initialState = Singleton (M.fromList (zip voc [0..]))
   in execWriter $ evalStateT (runReaderT
        (do
          (q, _) <- triple c T initialState
          q ==> F) id) ctx

commute, associate :: (St -> M (a, St)) -> St -> M (a, St)
commute ac (Composite st0 st1) = do
  (res, Composite st1' st0') <- ac (Composite st1 st0)
  pure (res, Composite st0' st1')
associate ac (Composite st0 (Composite st1 st2)) = do
  (res, Composite (Composite st0' st1') st2') <- ac (Composite (Composite st0 st1) st2)
  pure (res, Composite st0' (Composite st1' st2'))

rel :: M (St -> Prop)
rel = do
  c <- state (\ctx -> (relCount ctx, ctx { relCount = relCount ctx + 1 }))
  fSt <- ask
  pure (Rel c . collapse . fSt)
  where
    collapse :: St -> [Expr]
    collapse (Composite st0 st1) = collapse st0 ++ collapse st1
    collapse (Singleton m) = M.elems (M.mapWithKey (\v n -> V (v ++ "_" ++ show n)) m)

quantify :: Prop -> QProp
quantify p = Forall (S.toList (pvocab p)) p

(==>) :: Prop -> Prop -> M ()
(==>) p q = tell [quantify (p `Impl` q)]

equiv :: St -> St -> Prop
equiv st0 st1 = let (_, p, q) = resolve st0 st1 in p /\ q

resolve :: St -> St -> (St, Prop, Prop)
resolve (Composite st0 st1) (Composite st0' st1') =
  let (st0'', p0, p0') = resolve st0 st0'
      (st1'', p1, p1') = resolve st1 st1'
  in (Composite st0'' st1'', p0 /\ p1, p0' /\ p1')
resolve (Singleton m) (Singleton m') =
  let pairs = M.intersectionWith (,) m m'
      (m'', (p, p')) = runState (M.traverseWithKey merge pairs) (T, T)
   in (Singleton m'', p, p')
    where
      merge :: Var -> (Int, Int) -> State (Prop, Prop) Int
      merge v (n, m) = do
        let eql = Eql (V $ v ++ "_" ++ show n) (V $ v ++ "_" ++ show m)
        if n > m
           then modify (\(p, q) -> (p, q /\ eql))
           else if m > n
             then modify (\(p, q) -> (p /\ eql, q))
             else pure ()
        pure (max n m)


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
  Assign "i" (ALit 0) `Seq`
  Loop (Sum ( Assert (Lt (V "i") (V "n")) `Seq`
              Assign "s0" (Add (V "s0") (V "i")) `Seq`
              Assign "i" (Add (V "i") (ALit 1))
            ) (Assert (Ge (V "i") (V "n")))
    ) `Seq`
  Assert (Ge (V "i") (V "n")) `Seq`
  Assign "s1" (ALit (-1)) `Seq`
  Assign "s1" (Add (V "s1") (ALit 1)) `Seq`
  Assign "i1" (ALit 0) `Seq`
  Loop (Sum ( Assert (Lt (V "i1") (V "n")) `Seq`
              Assign "s1" (Add (V "s1") (V "i1")) `Seq`
              Assign "i1" (Add (V "i1") (ALit 1))
            ) (Assert (Ge (V "i1") (V "n")))
    ) `Seq`
  Assert (Ge (V "i1") (V "n")) `Seq`
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
