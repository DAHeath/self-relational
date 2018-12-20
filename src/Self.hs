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

erename :: Int -> Expr -> Expr
erename c = \case
  ALit i -> ALit i
  V v -> V (v ++ "_" ++ show c)
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


data St = Singleton Int (Map Var Expr) | Composite St St
type Vocab = [Var]

mkSingleton :: Int -> Vocab -> St
mkSingleton i v =
  Singleton i (M.fromList $ map (\v -> (v, V v)) v)

type Assertion = St -> Prop

-- | Commute the assertion: That is, swap how the assertion is applied to the
-- VarChange.
commute :: Assertion -> Assertion
commute p (Composite st1 st0) = p (Composite st0 st1)
commute _ _ = undefined

-- | Associate the assertion: That is, rotate how the assertion is applied to the
-- VarChange.
associate :: Assertion -> Assertion
associate p (Composite (Composite s0 s1) s2) = p (Composite s0 (Composite s1 s2))
associate _ _ = undefined

pand :: Prop -> Prop -> Prop
pand T p = p
pand p T = p
pand F _ = F
pand _ F = F
pand p q = p `And` q

mkImpl :: Assertion -> Assertion -> Assertion
mkImpl p0 p1 = \st -> p0 st `Impl` p1 st

pairwise :: Assertion -> Assertion -> Assertion
pairwise p0 p1 (Composite st0 st1) = p0 st0 `And` p1 st1
pairwise _ _ _ = undefined

left, right :: St -> Assertion -> Assertion
left st0 p = \st1 -> p (Composite st0 st1)
right st1 p = \st0 -> p (Composite st0 st1)

data Ctxt = Ctxt
  { _vocab :: Vocab
  , _theState :: St
  , _stateCount :: Int
  , _quantifiedState :: [St]
  }
makeLenses ''Ctxt

data QProp = Forall [Var] Prop
  deriving (Show, Read, Eq, Ord)

type M a = ReaderT Ctxt (StateT Int (Writer [QProp])) a

data Triple = Triple Assertion Com Assertion

rel :: M Assertion
rel = do
  q <- view quantifiedState
  c <- id <<+= 1
  pure (\st ->
    let es = enumerate (foldr Composite st q)
     in Rel c es)
  where
    enumerate :: St -> [Expr]
    enumerate (Singleton i st) = map (erename i) $ map snd $ M.toList st
    enumerate (Composite st0 st1) = enumerate st0 ++ enumerate st1

quantify :: Prop -> QProp
quantify p = Forall (S.toList (pvocab p)) p

(==>) :: Assertion -> Assertion -> M ()
(==>) a0 a1 = do
  st <- view theState
  let p = mkImpl a0 a1 st
  let ps = split p
  tell (map quantify ps)
   where
     split :: Prop -> [Prop]
     split (Impl p (And q r)) = split (Impl p q) ++ split (Impl p r)
     split p = [p]

(/\) :: Assertion -> Assertion -> Assertion
(/\) p q = \st -> p st `pand` q st

mkAssertion :: Prop -> Assertion
mkAssertion p = (\st -> case st of
  Singleton i st -> prename i (plookup st p)
  _ -> undefined)

equiv :: St -> St -> Prop
equiv (Composite st0 st1) (Composite st2 st3) = equiv st0 st2 `pand` equiv st1 st3
equiv (Singleton i st0) (Singleton j st1) =
    foldr (\v p -> eq1 i j st0 st1 v `pand` p) T (M.keys st0)
  where
    eq1 i j st0 st1 v =
      erename i (M.findWithDefault (V v) v st0)
      `Eql`
      erename j (M.findWithDefault (V v) v st1)


subst :: Var -> Expr -> Assertion -> Assertion
subst x e p = \case
  Singleton i st -> p (Singleton i (M.map (esubst x e) st))
  _ -> undefined

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

localLeft, localRight :: (St -> M a) -> M a
localLeft f = do
  (Composite st0 st1) <- view theState
  local ( (theState .~ st0)
        . (quantifiedState %~ (st1 :))
        ) (f st1)
localRight f = do
  (Composite st0 st1) <- view theState
  local ( (theState .~ st1)
        . (quantifiedState %~ (st0 :))
        ) (f st0)


localDouble :: M a -> M a
localDouble ac = do
  c <- view stateCount
  st <- view theState
  v <- view vocab
  let (st', c') = runState (go v st) c
  local ((stateCount .~ c') . (theState .~ (st `Composite` st'))) ac
  where
    go :: Vocab -> St -> State Int St
    go v (Singleton _ st) = do
      c <- id <<+= 1
      pure (mkSingleton c v)
    go v (Composite st0 st1) = Composite <$> go v st0 <*> go v st1

localCommute :: M a -> M a
localCommute ac = do
  (st0 `Composite` st1) <- view theState
  local (theState .~ (st1 `Composite` st0)) ac

localAssociate :: M a -> M a
localAssociate ac = do
  (st0 `Composite` (st1 `Composite` st2)) <- view theState
  local (theState .~ ((st0 `Composite` st1) `Composite` st0)) ac

initialCtxt :: Com -> Ctxt
initialCtxt c =
  let v =  S.toList $ cvocab c
  in Ctxt
     { _vocab = v
     , _theState = mkSingleton 0 v
     , _stateCount = 1
     , _quantifiedState = []
     }

triple :: Assertion -> Com -> Assertion -> M ()
triple p c q =
  case mergeLoops c of
    Skip -> p ==> q
    Assign x a -> p ==> (subst x a q)
    Assert e -> p /\ mkAssertion e ==> q
    Seq c0 c1 -> do
      if loopless c0 || loopless c1
      then do
        r <- rel
        triple p c0 r
        triple r c1 q
      else do
        localDouble (do
          r <- rel
          s <- rel
          q' <- rel
          localRight (\st0 -> triple (p /\ equiv st0) c0 (left st0 r))
          post <- localLeft (\st1 -> do
            triple (right st1 s) c1 (right st1 q')
            right st1 q' /\ equiv st1 ==> q)
          triple r (Prod c0 c1) s)
    Sum c0 c1 -> do
      triple p c0 q
      triple p c1 q
    Loop c -> do
      p ==> q
      triple q c q
    Prod c0 c1 ->
      if loopless c0 || loopless c1
      then do
        r <- rel
        localLeft (\st1 -> triple (right st1 p) c0 (right st1 r))
        localRight (\st0 -> triple (left st0 r) c1 (left st0 q))
      else
        case c1 of
          Sum c1' c1'' -> triple p (Sum (Prod c0 c1') (Prod c0 c1'')) q
          Prod c1' c1'' -> localAssociate (triple (associate p) (Prod (Prod c0 c1') c1'') (associate q))
          Loop c1' -> localCommute (triple (commute p) (Prod (Loop c1') c0) (commute q))
          Seq c1' c1'' ->
            if loopless c1'
            then triple p (Seq (Prod Skip c1') (Prod c0 c1'')) q
            else triple p (Seq (Prod c0 c1') (Prod Skip c1'')) q
          _ -> error ("Some impossible state has been reached: `" ++ showCom c ++ "`.")

hoare :: Com -> [QProp]
hoare c =
  let ctx = initialCtxt c
   in execWriter $ evalStateT (runReaderT
        (triple (mkAssertion T) c (mkAssertion F)) ctx) 0

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
  Assign "x" (Add (V "x") (ALit 1)) `Seq`
  Assign "x" (Add (V "x") (ALit 1)) `Seq`
  Assert (Not (Eql (V "x") (ALit 2)))

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
  Assert (Not (Eql (V "s0") (V "s1")))

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
