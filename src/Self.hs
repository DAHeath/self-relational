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
import           Data.List (intercalate, nub, groupBy)

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

esubst :: Map Var Expr -> Expr -> Expr
esubst m = \case
  ALit n -> ALit n
  V v -> M.findWithDefault (V v) v m
  Add a0 a1 -> Add (esubst m a0) (esubst m a1)

esimp :: Expr -> Expr
esimp (Add (ALit i) (ALit j)) = ALit (i + j)
esimp (Add e0 e1) = Add (esimp e0) (esimp e1)
esimp e = e

psubst :: Map Var Expr -> Prop -> Prop
psubst m = \case
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
    go = psubst m
    goe = esubst m

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
data St = Singleton (Map Var Expr) | Composite St St
  deriving (Show, Read, Eq, Ord)

-- | The context used to construct fresh variables. We include a counter for
-- fresh logical relations and a counter for fresh variables.
data Ctxt = Ctxt
  { relCount :: Int
  , varCount :: Int
  , vocab :: [Var]
  } deriving (Show, Read, Eq, Ord)

data Shape = Single | Multi Shape Shape
  deriving (Show, Read, Eq, Ord)

data Env = Env
  { quantification :: St -> St
  , shape :: Shape
  }

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
type M a = ReaderT Env (StateT Ctxt (Writer [QProp])) a

double :: Monad m => ReaderT Env m a -> ReaderT Env m a
double = local (\e -> e { shape = Multi (shape e) (shape e) })

quantifyLeft :: Monad m => St -> ReaderT Env m a -> ReaderT Env m a
quantifyLeft st = local (\case
  Env q (Multi _ s) -> Env (q . (st `Composite`)) s)

quantifyRight :: Monad m => St -> ReaderT Env m a -> ReaderT Env m a
quantifyRight st = local (\case
  Env q (Multi s _) -> Env (q . (`Composite` st)) s)

fresh :: M St
fresh = do
  sh <- asks shape
  go sh
  where
    go (Multi s0 s1) = Composite <$> go s0 <*> go s1
    go Single = do
      i <- state (\c -> (varCount c, c { varCount = varCount c + 1 }))
      voc <- lift $ gets vocab
      let m = M.fromList (zip voc (map (\v -> V (v ++ "_" ++ show i)) voc))
      pure (Singleton m)

type Assertion = St -> Prop

(***) :: Assertion -> Assertion -> Assertion
(***) p q = \case
  Composite st0 st1 -> p st0 /\ q st1
  s -> error (show s)

triple :: Assertion -> Com -> Assertion -> M ()
triple p c q
  | hasSummary c = do
     st <- fresh
     quant <- asks quantification
     let (r, st') = summary c st
     (p (quant st) /\ r) ==> q (quant st')
  | otherwise =
    case reassociate c of
      Seq c0 c1 ->
        if loopless c0 || loopless c1
        then do
          r <- rel
          triple p c0 r
          triple r c1 q
        else double $ do
          st <- fresh
          r <- rel
          s <- rel
          triple (p *** p) (Prod Skip c0) r
          triple r (Prod c0 c1) s
          triple s (Prod c1 Skip) (q *** q)
      Sum c0 c1 -> do
        triple p c0 q
        triple p c1 q
      Loop c -> do
        st <- fresh
        quant <- asks quantification
        p (quant st) ==> q (quant st)
        triple q c q
      Prod c0 c1 ->
        if loopless c0 || loopless c1
        then do
          Composite st0 st1 <- fresh
          r <- rel
          quantifyRight st1 (triple p c0 r)
          quantifyLeft st0 (triple r c1 q)
        else triple p (rewrite c0 c1) q

cseq :: Com -> Com -> Com
cseq Skip c = c
cseq c Skip = c
cseq c0 c1 = Seq c0 c1

reassociate :: Com -> Com
reassociate c = foldr cseq Skip (map (foldr cseq Skip) groups)
  where
    groups = groupBy (\c0 c1 -> hasSummary c0 && hasSummary c1) (deconstruct c)
    deconstruct (Seq c0 c1) = deconstruct c0 ++ deconstruct c1
    deconstruct c = [c]

summary :: Com -> St -> (Prop, St)
summary c st =
  case c of
    Skip -> (T, st)
    Assign x a ->
      let Singleton m = st
          a' = esubst m a
          m' = M.insert x a' m
      in (T, Singleton m')
    Assert p ->
      let Singleton m = st
       in (psubst m p, st)
    Seq c0 c1 ->
      let (p, st') = summary c0 st
          (q, st'') = summary c1 st'
      in (p /\ q, st'')
    Prod c0 c1 ->
      let Composite st0 st1 = st
          (p, st0') = summary c0 st0
          (q, st1') = summary c1 st1
       in (p /\ q, Composite st0' st1')

hasSummary :: Com -> Bool
hasSummary Skip = True
hasSummary Assign{} = True
hasSummary Assert{} = True
hasSummary (Seq c0 c1) = hasSummary c0 && hasSummary c1
hasSummary (Prod c0 c1) = hasSummary c0 && hasSummary c1
hasSummary _ = False

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
      ctx = Ctxt
        { relCount = 0
        , varCount = 1
        , vocab = voc
        }
   in execWriter $ evalStateT (runReaderT
        (triple (const T) c (const F)) (Env id Single)) ctx

rel :: M (St -> Prop)
rel = do
  c <- state (\ctx -> (relCount ctx, ctx { relCount = relCount ctx + 1 }))
  fSt <- asks quantification
  pure (Rel c . collapse . fSt)
  where
    collapse :: St -> [Expr]
    collapse (Composite st0 st1) = collapse st0 ++ collapse st1
    collapse (Singleton m) = M.elems m

quantify :: Prop -> QProp
quantify p = Forall (S.toList (pvocab p)) p

(==>) :: Prop -> Prop -> M ()
(==>) p q = tell [quantify (psimp (p `Impl` q))]

equiv :: St -> St -> Prop
equiv (Composite st0 st1) (Composite st0' st1') = equiv st0 st0' /\ equiv st1 st1'
equiv (Singleton m0) (Singleton m1) =
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
  Assign "i" (ALit 1) `Seq`
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
