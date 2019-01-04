{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}
module Self where

import Control.Lens
import Control.Monad.State
import Control.Monad.Writer hiding (Sum)
import Control.Monad.Reader
import qualified Data.Set as S
import           Data.Set (Set)
import           Data.List (intercalate)

import Debug.Trace

data Kind = INT | ARRAY
  deriving (Show, Read, Eq, Ord)

data Var = Var String Kind
  deriving (Show, Read, Eq, Ord)

kind :: Var -> Kind
kind (Var _ k) = k

-- | The space of arithmetic expressions.
data Expr
  = ALit Integer
  | Add Expr Expr
  | V Var
  | Store Expr Expr Expr
  | Select Expr Expr
  deriving (Show, Read, Eq, Ord)

exprKind :: Expr -> Kind
exprKind = \case
  ALit _ -> INT
  Add{} -> INT
  V (Var _ k) -> k
  Store{} -> ARRAY
  Select{} -> INT

esubst :: Var -> Expr -> Expr -> Expr
esubst x e = \case
  ALit i -> ALit i
  Add e0 e1 -> Add (go e0) (go e1)
  V v -> if v == x then e else V v
  Store e0 e1 e2 -> Store (go e0) (go e1) (go e2)
  Select e0 e1 -> Select (go e0) (go e1)
  where
    go = esubst x e

vrename :: Int -> Var -> Var
vrename c (Var v k) = Var (v ++ "_" ++ show c) k

erename :: Int -> Expr -> Expr
erename c = \case
  ALit i -> ALit i
  V v -> V (vrename c v)
  Add a0 a1 -> Add (erename c a0) (erename c a1)
  Store a0 a1 a2 -> Store (erename c a0) (erename c a1) (erename c a2)
  Select a0 a1 -> Select (erename c a0) (erename c a1)

evocab :: Expr -> Set Var
evocab = \case
  V v -> S.singleton v
  Add e0 e1 -> S.union (evocab e0) (evocab e1)
  Store e0 e1 e2 -> S.unions [evocab e0, evocab e1, evocab e2]
  Select e0 e1 -> S.union (evocab e0) (evocab e1)
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
  | Star
  deriving (Show, Read, Eq, Ord)

pand :: Prop -> Prop -> Prop
pand T p = p
pand p T = p
pand F _ = F
pand _ F = F
pand p q = p `And` q

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
  Star -> Star
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
  Star -> Star
  where
    go = prename i
    goe = erename i

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
  Star -> S.empty

propRels :: Prop -> Set (ID, [Kind])
propRels = \case
  T -> S.empty
  F -> S.empty
  Not p -> propRels p
  And p0 p1 -> propRels p0 `S.union` propRels p1
  Impl p0 p1 -> propRels p0 `S.union` propRels p1
  Eql{} -> S.empty
  Lt{} -> S.empty
  Ge{} -> S.empty
  Rel i es -> S.singleton (i, map exprKind es)
  Star -> S.empty

-- | The space of non-deterministic imperative commands.
data Com
  = Assign Var Expr
  | Havoc Var
  | Assert Prop
  | Skip
  | Seq Com Com
  | If Prop Com Com
  | Sum Com Com
  | Prod Com Com
  | While [(Prop, Com)]
  deriving (Show, Read, Eq, Ord)

mseq :: [Com] -> Com
mseq = foldr1 Seq

cvocab :: Com -> Set Var
cvocab = \case
  Assign v e -> S.insert v $ evocab e
  Havoc v -> S.singleton v
  Assert p -> pvocab p
  Skip -> S.empty
  Seq c0 c1 -> cvocab c0 `S.union` cvocab c1
  If p c0 c1 -> pvocab p `S.union` cvocab c0 `S.union` cvocab c1
  Sum c0 c1 -> cvocab c0 `S.union` cvocab c1
  Prod c0 c1 -> cvocab c0 `S.union` cvocab c1
  While bodies -> foldMap (\(b, c) -> pvocab b `S.union` cvocab c) bodies

loopless :: Com -> Bool
loopless = \case
  While{} -> False
  If _ c0 c1 -> loopless c0 && loopless c1
  Sum c0 c1 -> loopless c0 && loopless c1
  Prod c0 c1 -> loopless c0 && loopless c1
  Seq c0 c1 -> loopless c0 && loopless c1
  Assert{} -> True
  Assign{} -> True
  Havoc{} -> True
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
         (While b0, While b1) -> While (b0 ++ b1)
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

temporary :: Kind -> M Var
temporary k = do
  c <- temporaryCount <<+= 1
  pure (Var ("V" ++ show c) k)

quantify :: Prop -> QProp
quantify p = Forall (S.toList (pvocab p)) p

(/\) :: [Prop] -> Prop -> [Prop]
(/\) ps p = map (`pand` p) ps

(==>) :: [Prop] -> Prop -> M ()
(==>) ps q = mapM_ (\p ->tell [quantify (p `Impl` q)]) ps

equiv :: St -> St -> M Prop
equiv (Composite st0 st1) (Composite st2 st3) = pand <$> equiv st0 st2 <*> equiv st1 st3
equiv (Singleton i) (Singleton j) = do
  voc <- view vocab
  pure (foldr (\v p -> eq1 i j (V v) `pand` p) T voc)
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

triple :: Com -> [Prop] -> M [Prop]
triple c p =
  traceM (showCom c) >> traceM "" >>
  case mergeLoops c of
    Skip -> pure p
    Assign x a -> do
      t <- temporary (kind x)
      Singleton st <- view theState
      let x' = vrename st x
      pure $
        map (\p -> psubst x' (V t) p `pand` (Eql (V x') (esubst x' (V t) (erename st a)))) p
    Havoc x -> do
      t <- temporary (kind x)
      Singleton st <- view theState
      let x' = vrename st x
      pure $ map (\p -> psubst x' (V t) p) p
    Assert Star -> pure p
    Assert (Not Star) -> pure p
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
    If b c0 c1 ->
      triple (Sum (Seq (Assert b) c0) (Seq (Assert (Not b)) c1)) p
    Sum c0 c1 -> do
      q0 <- triple c0 p
      q1 <- triple c1 p
      pure (q0 ++ q1)
    While bodies -> do
      r <- rel
      p ==> r
      let (exit : cs) =
            map (foldr1 Prod) $
            sequence $
            map (\(b, c) -> [Assert (Not b), Seq (Assert b) c]) bodies
      qs <- traverse (`triple` [r]) cs
      concat qs ==> r
      triple exit [r]
    Prod c0 c1 ->
      if loopless c0 || loopless c1
      then do
        r <- left (triple c0 p)
        right (triple c1 r)
      else
        case c1 of
          If b c1' c1'' ->
            triple (Prod c0 (Sum (Seq (Assert b) c1') (Seq (Assert (Not b)) c1''))) p
          Sum c1' c1'' -> triple (Sum (Prod c0 c1') (Prod c0 c1'')) p
          Prod c1' c1'' -> associate (triple (Prod (Prod c0 c1') c1'') p)
          While c1' -> commute (triple (Prod c1 c0) p)
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
          qs <- triple c [T]
          qs ==> F) ctx) initialCtxt

point, heap :: Var
point = Var "POINT" INT
heap = Var "HEAP" ARRAY

initializeHeap :: Com
initializeHeap = Assign point (ALit 1)

alloc :: Integer -> Var -> Com
alloc n v =
  Seq
    (Assign v (V point))
    (Assign point (Add (V point) (ALit n)))

save :: Expr -> Expr -> Com
save addr val = Assign heap (Store (V heap) addr val)

load :: Expr -> Expr
load addr = Select (V heap) addr

showCom :: Com -> String
showCom = \case
  Skip -> "skip"
  Assign (Var v _) e -> v ++ " := " ++ smt2Expr e
  Havoc (Var v _) -> "havoc " ++ v
  Assert e -> "assert " ++ smt2Prop e
  Seq c0 c1 -> showCom c0 ++ ";\n" ++ showCom c1
  Sum c0 c1 -> "{" ++ showCom c0 ++ "} +\n {" ++ showCom c1 ++ "}"
  Prod c0 c1 -> "{" ++ showCom c0 ++ "} *\n {" ++ showCom c1 ++ "}"
  While bs -> "While {\n" ++
    intercalate "\n  " (map showBody bs) ++ "}"
      where showBody :: (Prop, Com) -> String
            showBody (p, c) = smt2Prop p ++ " -> " ++ showCom c

sexpr :: [String] -> String
sexpr ss = "(" ++ unwords ss ++ ")"

smt2 :: Com -> String
smt2 c = unlines [header, decls, body, footer]
  where
    header = unlines [ sexpr ["set-logic", "HORN"]
                     , sexpr ["set-option", ":fixedpoint.engine", "\"duality\""]
                     ]
    footer = unlines [ sexpr ["check-sat"], sexpr ["get-model"] ]
    decl (i, ks) = sexpr ["declare-fun", "R" ++ show i, sexpr (map smt2Kind ks), "Bool"]
    decls = unlines $ map decl (S.toList rels)
    body = unlines (map smt2QProp qs)
    qs = hoare c
    rels = S.unions (map qrels qs)
    qrels (Forall _ p) = propRels p

smt2Kind :: Kind -> String
smt2Kind = \case
  INT -> "Int"
  ARRAY -> "(Array Int Int)"

smt2QProp :: QProp -> String
smt2QProp (Forall vs p) = sexpr ["assert", body] ++ "\n"
  where
    body = case vs of
             [] -> smt2Prop p
             _ -> sexpr ["forall", (sexpr $ map var vs) ++ "\n", "  " ++ smt2Prop p]
    var (Var v k) = sexpr [v, smt2Kind k]

smt2Expr :: Expr -> String
smt2Expr = \case
  ALit i -> show i
  Add a0 a1 -> sexpr ["+", smt2Expr a0, smt2Expr a1]
  Store a0 a1 a2 -> sexpr ["store", smt2Expr a0, smt2Expr a1, smt2Expr a2]
  Select a0 a1 -> sexpr ["select", smt2Expr a0, smt2Expr a1]
  V (Var v _) -> v

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
  Star -> undefined
  where
    conjuncts :: Prop -> [Prop]
    conjuncts (And p0 p1) = conjuncts p0 ++ conjuncts p1
    conjuncts p = [p]

-- example :: Com
-- example =
--   Assign "x" (ALit 0) `Seq`
--   Assign "x" (Add (V "x") (ALit 1)) `Seq`
--   -- Assign "x" (Add (V "x") (ALit 1)) `Seq`
--   Assert (Not (Eql (V "x") (ALit 1)))

-- example2 :: Com
-- example2 =
--   If (Eql (V "x") (ALit 0))
--      (Assign "x" (ALit 0))
--      (Assign "x" (ALit 1)) `Seq`
--   Assert (Lt (V "x") (ALit 0))

example3 :: Com
example3 =
  mseq
    [ Assign s0 (ALit 0)
    , Assign s1 (ALit 0)
    , Assign i0 (ALit 0)
    -- , Assign i1 (ALit 0)
    , While [
      ( Lt (V i0) (V n)
      , Assign s0 (Add (V s0) (V i0)) `Seq`
        Assign i0 (Add (V i0) (ALit 1))
      )]
    , Assign i1 (ALit 0)
    , While [
      ( Lt (V i1) (V n)
      , Assign s1 (Add (V s1) (V i1)) `Seq`
        Assign i1 (Add (V i1) (ALit 1))
      )]
    , Assert (Not (Eql (V s0) (V s1)))
    ]
  where
    s0 = Var "s0" INT
    s1 = Var "s1" INT
    i0 = Var "i0" INT
    i1 = Var "i1" INT
    n = Var "n" INT

buildInspect :: Com
buildInspect =
  mseq
    [ initializeHeap
    , alloc 1 a
    , Assign b (V a)
    , While [(
        Star,
        mseq
          [ alloc 1 x
          , save (V b) (V x)
          , Assign b (V x)
          ]
       )]
    , save (V b) (ALit 0)
    , While [(
        Not (Eql (V a) (V b)),
        Assign a (load (V a))
       )]
    , Assert (Not (Eql (load (V a)) (ALit 0)))
    ]
  where
    a = Var "a" INT
    b = Var "b" INT
    x = Var "x" INT

triangleList :: Com
triangleList =
  mseq
    [ initializeHeap
    , alloc 2 head
    , Assign tail (V head)
    , Assign i (ALit 0)
    , While [(Lt (V i) (V n),
        mseq
          [ save (V tail) (V i)
          , alloc 2 tmp
          , save (Add (V tail) (ALit 1)) (V tmp)
          , Assign tail (V tmp)
          , Assign i (Add (V i) (ALit 1))
          ]
      )]
    , Assign i (ALit 0)
    , Assign s0 (ALit 0)
    , Assign s1 (ALit 0)
    , While [(Not (Eql (V head) (V tail)),
        mseq
          [ Assign s0 (Add (V s0) (V i))
          , Assign s1 (Add (V s1) (load (V head)))
          , Assign head (load (Add (V head) (ALit 1)))
          , Assign i (Add (V i) (ALit 1))
          ]
      )]
    , Assert (Not (Eql (V s0) (V s1)))
    ]
  where
    head = Var "head" INT
    tail = Var "tail" INT
    s0 = Var "s0" INT
    s1 = Var "s1" INT
    tmp = Var "tmp" INT
    i = Var "i" INT
    n = Var "n" INT

listSum :: Com
listSum =
  mseq
    [ initializeHeap
    , alloc 2 head
    , Assign tail (V head)
    , Assign s0 (ALit 0)
    , Assign i (ALit 0)
    , While [(Lt (V i) (V n),
        mseq
          [ Havoc x
          , Assign s0 (Add (V s0) (V x))
          , alloc 2 tmp
          , save (V tail) (V x)
          , save (Add (V tail) (ALit 1)) (V tmp)
          , Assign tail (V tmp)
          , Assign i (Add (V i) (ALit 1))
          ]
        )]
    , Assign s1 (ALit 0)
    , Assign i (ALit 0)
    , While [(Lt (V i) (V n),
          mseq
            [ Assign s1 (Add (V s1) (load (V head)))
            , Assign head (load (Add (V head) (ALit 1)))
            , Assign i (Add (V i) (ALit 1))
            ]
        )]
    , Assert (Not (Eql (V s0) (V s1)))
    ]
  where
    head = Var "head" INT
    tail = Var "tail" INT
    tmp = Var "tmp" INT
    s0 = Var "s0" INT
    s1 = Var "s1" INT
    x = Var "x" INT
    i = Var "i" INT
    n = Var "n" INT
