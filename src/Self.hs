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
import           Data.List (intercalate)

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

vrename :: Int -> Var -> Var
vrename c v = v ++ "_" ++ show c

erename :: Int -> Expr -> Expr
erename c = \case
  ALit i -> ALit i
  V v -> V (vrename c v)
  Add a0 a1 -> Add (erename c a0) (erename c a1)

elookup :: (Map Var Expr) -> Expr -> Expr
elookup m = \case
  ALit i -> ALit i
  V v -> M.findWithDefault (V v) v m
  Add a0 a1 -> Add (elookup m a0) (elookup m a1)

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

(/\) :: Prop -> Prop -> Prop
(/\) T p = p
(/\) p T = p
(/\) F _ = F
(/\) _ F = F
(/\) p q = p `And` q

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

prename :: Int -> Prop -> Prop
prename i = \case
  T -> T
  F -> F
  Not p -> Not (go p)
  And p0 p1 -> And (go p0) (go p1)
  Impl p0 p1 -> Impl (go p0) (go p1)
  Eql e0 e1 -> Eql (goe e0) (goe e1)
  Lt e0 e1 -> Lt (goe e0) (goe e1)
  Ge e0 e1 -> Ge (goe e0) (goe e1)
  where
    go = prename i
    goe = erename i

plookup :: (Map Var Expr) -> Prop -> Prop
plookup m = \case
  T -> T
  F -> F
  Not p -> Not (go p)
  And p0 p1 -> And (go p0) (go p1)
  Impl p0 p1 -> Impl (go p0) (go p1)
  Eql e0 e1 -> Eql (goe e0) (goe e1)
  Lt e0 e1 -> Lt (goe e0) (goe e1)
  Ge e0 e1 -> Ge (goe e0) (goe e1)
  where
    go = plookup m
    goe = elookup m

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
         (Loop c0, Loop c1) ->
           Loop (Prod c0 c1)
             -- Sum [ Prod c0 c1
             --     , Prod c0 Skip
             --     , Prod Skip c1
             --     ])
         _ -> Prod c0' c1'
  c -> c

data St = Singleton Int | Composite St St
  deriving (Show, Read, Eq, Ord)
type Vocab = [Var]

data Env = Env
  { _vocab :: Vocab
  , _theState :: St
  , _activeState :: [Int]
  } deriving (Show, Read, Eq, Ord)

initialEnv :: Com -> Env
initialEnv c =
  let v =  S.toList $ cvocab c
  in Env
     { _vocab = v
     , _theState = Singleton 0
     , _activeState = [0]
     }

data Ctxt = Ctxt
  { _relCount :: Int
  , _temporaryCount :: Int
  , _stateCount :: Int
  } deriving (Show, Read, Eq, Ord)

initialCtxt :: Ctxt
initialCtxt = Ctxt 0 0 1

makeLenses ''Env
makeLenses ''Ctxt

data QProp = Forall [Var] Prop
  deriving (Show, Read, Eq, Ord)

type M a = ReaderT Env (StateT Ctxt (Writer [QProp])) a

commute, associate, left, right :: M a -> M a
commute = local (theState %~ \(Composite st0 st1) -> Composite st1 st0)
associate = local (theState %~
  \(Composite st0 (Composite st1 st2)) -> Composite (Composite st0 st1) st2)
left = local (theState %~ \(Composite st0 _) -> st0)
right = local (theState %~ \(Composite _ st1) -> st1)

rel :: M Prop
rel = do
  act <- view activeState
  v <- view vocab
  c <- relCount <<+= 1
  let es = concatMap (\i -> map (erename i . V) v) act
  pure (Rel c es)

temporary :: M Var
temporary = do
  c <- temporaryCount <<+= 1
  pure ("V" ++ show c)

quantify :: Prop -> QProp
quantify p = Forall (S.toList (pvocab p)) p

(==>) :: Prop -> Prop -> M ()
(==>) p q = tell [quantify (p `Impl` q)]

equiv :: St -> St -> M Prop
equiv (Composite st0 st1) (Composite st2 st3) = (/\) <$> equiv st0 st2 <*> equiv st1 st3
equiv (Singleton i) (Singleton j) = do
  voc <- view vocab
  pure (foldr (\v p -> eq1 i j (V v) /\ p) T voc)
  where eq1 i j v = erename i v `Eql` erename j v

double :: M a -> M a
double ac = do
  st <- view theState
  st' <- go st
  local ( (activeState <>~ flatten st')
        . (theState .~ (st `Composite` st'))
        ) ac
  where
    go :: St -> M St
    go (Singleton _) = do
      c <- stateCount <<+= 1
      pure (Singleton c)
    go (Composite st0 st1) = Composite <$> go st0 <*> go st1
    flatten :: St -> [Int]
    flatten (Singleton c) = [c]
    flatten (Composite st0 st1) = flatten st0 ++ flatten st1

triple :: Com -> Prop -> M Prop
triple c p =
  case mergeLoops c of
    Skip -> pure p
    Assign x a -> do
      t <- temporary
      Singleton st <- view theState
      let x' = vrename st x
      pure $ psubst x' (V t) p /\ (Eql (V x') (esubst x' (V t) (erename st a)))
    Assert e -> do
      Singleton st <- view theState
      pure (p /\ (prename st e))
    Seq c0 c1 ->
      if | looplessStart c0 ->
            case c0 of
              Seq c0' c0'' -> triple (Seq c0' (Seq c0'' c1)) p
              c -> triple c0 p >>= triple c1
         | looplessEnd c1 ->
            case c1 of
              Seq c1' c1'' -> triple (Seq (Seq c0 c1') c1'') p
              c -> triple c0 p >>= triple c1
         | otherwise ->
            double (do
              Composite st0 st1 <- view theState
              eq <- equiv st0 st1
              q <- triple (Prod Skip c0) (p /\ eq)
                    >>= triple (Prod c0 c1)
                    >>= triple (Prod c1 Skip)
              pure (q /\ eq))
    Sum c0 c1 -> do
      q0 <- triple c0 p
      q1 <- triple c1 p
      q <- rel
      q0 ==> q
      q1 ==> q
      pure q
    Loop c -> do
      r <- rel
      p ==> r
      q <- triple c r
      q ==> r
      pure r
    Prod c0 c1 ->
      if loopless c0 || loopless c1
      then do
        r <- left (triple c0 p)
        right (triple c1 r)
      else
        case c1 of
          Sum c1' c1'' -> triple (Sum (Prod c0 c1') (Prod c0 c1'')) p
          Prod c1' c1'' -> associate (triple (Prod (Prod c0 c1') c1'') p)
          Loop c1' -> commute (triple (Prod (Loop c1') c0) p)
          Seq c1' c1'' ->
            if loopless c1'
            then triple (Seq (Prod Skip c1') (Prod c0 c1'')) p
            else triple (Seq (Prod c0 c1') (Prod Skip c1'')) p
          _ -> error ("Some impossible state has been reached: `" ++ showCom c ++ "`.")

hoare :: Com -> [QProp]
hoare c =
  let ctx = initialEnv c
   in execWriter $ evalStateT (runReaderT
        (do
          q <- triple c T
          q ==> F) ctx) initialCtxt

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
  And p0 p1 -> sexpr ("and" : map smt2Prop (conjuncts p0 ++ conjuncts p1))
  Impl p0 p1 -> sexpr ["=>", smt2Prop p0, smt2Prop p1]
  Eql e0 e1 -> sexpr ["=", smt2Expr e0, smt2Expr e1]
  Lt e0 e1 -> sexpr ["<", smt2Expr e0, smt2Expr e1]
  Ge e0 e1 -> sexpr [">=", smt2Expr e0, smt2Expr e1]
  Rel i es -> sexpr (("R" ++ show i) : map smt2Expr es)
  where
    conjuncts :: Prop -> [Prop]
    conjuncts (And p0 p1) = conjuncts p0 ++ conjuncts p1
    conjuncts p = [p]

example :: Com
example =
  Assign "x" (ALit 0) `Seq`
  Assign "x" (Add (V "x") (ALit 1)) `Seq`
  -- Assign "x" (Add (V "x") (ALit 1)) `Seq`
  Assert (Not (Eql (V "x") (ALit 1)))

example2 :: Com
example2 =
  Sum (Assign "x" (ALit 0))
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
    Sum
      (Assert (Lt (V "i0") (V "n")) `Seq`
        Assign "s0" (Add (V "s0") (V "i0")) `Seq`
        Assign "i0" (Add (V "i0") (ALit 1)))
      (Assert (Ge (V "i0") (V "n")))
  ) `Seq`
  Assert (Ge (V "i0") (V "n")) `Seq`
  Loop (
    Sum
      (Assert (Lt (V "i1") (V "n")) `Seq`
        Assign "s1" (Add (V "s1") (V "i1")) `Seq`
        Assign "i1" (Add (V "i1") (ALit 1)))
      (Assert (Ge (V "i1") (V "n")))
  ) `Seq`
  Assert (Ge (V "i1") (V "n")) `Seq`
  Assert (Not (Eql (V "s0") (V "s1")))

example4 :: Com
example4 =
  Assign "s0" (ALit 0) `Seq`
  Assign "s1" (ALit 0) `Seq`
  Assign "i0" (ALit 0) `Seq`
  Assign "i1" (ALit 0) `Seq`
  Loop (
    Sum
      (Assert (Lt (V "i0") (V "n")) `Seq`
        Assign "s0" (Add (V "s0") (V "i0")) `Seq`
        Assign "i0" (Add (V "i0") (ALit 1)))
      (Assert (Ge (V "i0") (V "n")))
  ) `Seq`
  Assert (Ge (V "i0") (V "n")) `Seq`

  Loop (
    Sum
      (Assert (Lt (V "i1") (V "n")) `Seq`
        Assign "s1" (Add (V "s1") (V "i1")) `Seq`
        Assign "i1" (Add (V "i1") (ALit 1)))
      (Assert (Ge (V "i1") (V "n")))
  ) `Seq`
  Assert (Ge (V "i1") (V "n")) `Seq`

  Assign "s2" (ALit 0) `Seq`
  Assign "s3" (ALit 0) `Seq`
  Assign "i2" (ALit 0) `Seq`
  Loop (
    Sum
      (Assert (Lt (V "i2") (V "n")) `Seq`
        Assign "s2" (Add (V "s2") (V "i2")) `Seq`
        Assign "s3" (Add (V "s3") (V "i2")) `Seq`
        Assign "i2" (Add (V "i2") (ALit 1)))
      (Assert (Ge (V "i2") (V "n")))
  ) `Seq`
  Assert (Ge (V "i2") (V "n")) `Seq`

  Assert (Not (And
    (Eql (V "s0") (V "s2"))
    (Eql (V "s1") (V "s3"))))
