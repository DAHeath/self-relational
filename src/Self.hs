{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}
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
import           Data.List (intercalate, nub)

import Debug.Trace

type Var = String

-- | The space of arithmetic expressions.
data Expr
  = ALit Integer
  | Add Expr Expr
  | V Var
  deriving (Show, Read, Eq, Ord)

vrename :: Map Var Int -> Var -> Var
vrename m v = (v ++ "_" ++ show (M.findWithDefault 0 v m))

erename :: Map Var Int -> Expr -> Expr
erename m = \case
  ALit i -> ALit i
  V v -> V (vrename m v)
  Add a0 a1 -> Add (erename m a0) (erename m a1)

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
  | Or Prop Prop
  | Impl Prop Prop
  | Eql Expr Expr
  | Lt Expr Expr
  | Ge Expr Expr
  | Rel ID [Expr]
  deriving (Show, Read, Eq, Ord)

(/\) :: Prop -> Prop -> Prop
(/\) T p = p
(/\) p T = p
(/\) F _ = F
(/\) _ F = F
(/\) p q = p `And` q

(\/) :: Prop -> Prop -> Prop
(\/) T _ = T
(\/) _ T = T
(\/) F p = p
(\/) p F = p
(\/) p q = p `Or` q

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

looplessStart :: Com -> Bool
looplessStart = \case
  Seq c0 _ -> looplessStart c0
  c -> loopless c

looplessEnd :: Com -> Bool
looplessEnd = \case
  Seq _ c1 -> looplessEnd c1
  c -> loopless c

mergeLoops :: Com -> Com
mergeLoops = \case
  Prod c0 c1 ->
    let c0' = mergeLoops c0
        c1' = mergeLoops c1
    in case (c0', c1') of
         (Loop c0, Loop c1) -> Loop (c0 `Prod` c1)
         _ -> Prod c0' c1'
  c -> c

data St = Singleton (Map Var Int) | Composite St St
  deriving (Show, Read, Eq, Ord)

type Vocab = [Var]

data Env = Env
  { _vocab :: Vocab
  , _ambient :: [St]
  } deriving (Show, Read, Eq, Ord)

initialEnv :: Com -> Env
initialEnv c =
  let v = S.toList $ cvocab c
  in Env
     { _vocab = v
     , _ambient = []
     }

data Ctxt = Ctxt
  { _relCount :: Int
  , _varCount :: Int
  } deriving (Show, Read, Eq, Ord)

initialCtxt :: Com -> Ctxt
initialCtxt c =
  let v = S.toList $ cvocab c
   in Ctxt
      { _relCount = 0
      , _varCount = length v
      }

makeLenses ''Env
makeLenses ''Ctxt

data QProp = Forall [Var] Prop
  deriving (Show, Read, Eq, Ord)

type M a = ReaderT Env (StateT Ctxt (Writer [QProp])) a

commute, associate :: (St -> M (a, St)) -> St -> M (a, St)
commute ac (Composite st0 st1) = do
  (res, Composite st1' st0') <- ac (Composite st1 st0)
  pure (res, Composite st0' st1')
associate ac (Composite st0 (Composite st1 st2)) = do
  (res, Composite (Composite st0' st1') st2') <- ac (Composite (Composite st0 st1) st2)
  pure (res, Composite st0' (Composite st1' st2'))

rel :: M (St -> Prop)
rel = do
  c <- relCount <<+= 1
  amb <- concatMap collapse <$> view ambient
  pure (\st -> Rel c (collapse st ++ amb))
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

copy :: St -> M St
copy (Composite st0 st1) = Composite <$> copy st0 <*> copy st1
copy (Singleton m) = Singleton <$> traverse (\_ -> varCount <<+= 1) m

triple :: Com -> Prop -> St -> M (Prop, St)
triple c p st
  | loopless c = do
    (q, st') <- summary c st
    pure (p /\ q, st')
  | otherwise = case mergeLoops c of
    Seq c0 c1 ->
      if | looplessStart c0 ->
            case c0 of
              Seq c0' c0'' -> triple (Seq c0' (Seq c0'' c1)) p st
              c -> do
                (q, st') <- triple c0 p st
                (r, st'') <- triple c1 q st'
                pure (r, st'')
         | looplessEnd c1 ->
            case c1 of
              Seq c1' c1'' -> triple (Seq (Seq c0 c1') c1'') p st
              c -> do
                (q, st') <- triple c0 p st
                (r, st'') <- triple c1 q st'
                pure (r, st'')
         | otherwise -> do
           (q, st') <- triple (Prod Skip c0) p (Composite st st)
           (r, st'') <- triple (Prod c0 c1) q st'
           (s, Composite st0 st1) <- triple (Prod c1 Skip) r st''
           pure (s /\ equiv st0 st1, st0)
    Sum c0 c1 -> do
      (q0, st0) <- triple c0 p st
      (q1, st1) <- triple c1 p st
      let (st', r0, r1) = resolve st0 st1
      pure ((q0 /\ r0) \/ (q1 /\ r1), st')
    Loop c -> do
      r <- rel
      p ==> r st
      (q, st') <- triple c (r st) st
      q ==> r st'
      pure (r st', st')
    Prod c0 c1 ->
      if loopless c0 || loopless c1
      then do
        let Composite st0 st1 = st
        st0Cop <- copy st0
        st1Cop <- copy st1
        (q0, st0') <- local (ambient %~ (st1:)) (triple c0 p st0)
        (q1, st1') <- local (ambient %~ (st0:)) (triple c1 p st1)
        pure (q0 /\ q1, Composite st0' st1')
      else case c1 of
        Sum c1' c1'' -> triple (Sum (Prod c0 c1') (Prod c0 c1'')) p st
        Prod c1' c1'' -> associate (triple (Prod (Prod c0 c1') c1'') p) st
        Loop c1' -> commute (triple (Prod (Loop c1') c0) p) st
        Seq c1' c1'' ->
          if loopless c1'
          then triple (Seq (Prod Skip c1') (Prod c0 c1'')) p st
          else triple (Seq (Prod c0 c1') (Prod Skip c1'')) p st
        _ -> error ("Some impossible state has been reached: `" ++ showCom c ++ "`.")

summary :: Com -> St -> M (Prop, St)
summary c st = case c of
  Skip -> pure (T, st)
  Assign x a -> do
    let Singleton m = st
    v <- varCount <<+= 1
    let m' = M.insert x v m
    pure (Eql (erename m' (V x)) (erename m a), Singleton m')
  Assert e -> do
    let Singleton m = st
    pure (prename m e, st)
  Seq c0 c1 -> do
    (p, st') <- summary c0 st
    (q, st'') <- summary c1 st'
    pure (p /\ q, st'')
  Sum c0 c1 -> do
    (p0, st0) <- summary c0 st
    (p1, st1) <- summary c1 st
    let (st', q0, q1) = resolve st0 st1
    pure ((p0 /\ q0) \/ (p1 /\ q1), st')
  Prod c0 c1 -> do
    let Composite st0 st1 = st
    (p0, st0') <- summary c0 st0
    (p1, st1') <- summary c1 st1
    pure (p0 /\ p1, Composite st0' st1')

hoare :: Com -> [QProp]
hoare c =
  let env = initialEnv c
      ctx = initialCtxt c
      initialState = Singleton (M.fromList (zip (view vocab env) [0..]))
   in execWriter $ evalStateT (runReaderT
        (do
          (q, _) <- triple c T initialState
          q ==> F) env) (initialCtxt c)

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

  Assert (Not (Eql (V "s0") (V "s2"))) `Seq`
  Assert (Not (Eql (V "s1") (V "s3")))
