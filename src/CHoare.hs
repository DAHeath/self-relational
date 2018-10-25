{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
module CHoare where

import           Control.Monad.State
import           Control.Monad.Writer
import           Control.Monad.Reader
import qualified Data.Set as S
import           Data.Set (Set)
import qualified Data.Map as M
import           Data.Map (Map)
import           Prelude hiding (seq)
import           Data.Maybe (mapMaybe, listToMaybe)

type Var = String

data Expr
  = Add Expr Expr
  | Mul Expr Expr
  | Sub Expr Expr
  | Div Expr Expr
  | Lit Integer
  | V Var
  deriving (Show, Read, Eq, Ord)

evocab :: Expr -> Set Var
evocab = \case
  Add e1 e2 -> evocab e1 `S.union` evocab e2
  Mul e1 e2 -> evocab e1 `S.union` evocab e2
  Sub e1 e2 -> evocab e1 `S.union` evocab e2
  Div e1 e2 -> evocab e1 `S.union` evocab e2
  Lit _ -> S.empty
  V v -> S.singleton v

esubst :: Var -> Expr -> Expr -> Expr
esubst v e = \case
  Add e1 e2 -> Add (esubst v e e1) (esubst v e e2)
  Mul e1 e2 -> Mul (esubst v e e1) (esubst v e e2)
  Sub e1 e2 -> Sub (esubst v e e1) (esubst v e e2)
  Div e1 e2 -> Div (esubst v e e1) (esubst v e e2)
  Lit i -> Lit i
  V v' -> if v == v' then e else V v'

data Prop
  = PTrue
  | PFalse
  | PImpl Prop Prop
  | PAnd Prop Prop
  | PNot Prop
  | PEql Expr Expr
  | PLt Expr Expr
  | PRel Var [Expr]
  | PForall Var Prop
  | PProd Prop Prop {- NEW -}
  deriving (Show, Read, Eq, Ord)

pvocab :: Prop -> Set Var
pvocab = \case
  PTrue -> S.empty
  PFalse -> S.empty
  PImpl p1 p2 -> pvocab p1 `S.union` pvocab p2
  PAnd p1 p2 -> pvocab p1 `S.union` pvocab p2
  PNot p -> pvocab p
  PEql e1 e2 -> evocab e1 `S.union` evocab e2
  PLt e1 e2 -> evocab e1 `S.union` evocab e2
  PRel v es -> S.unions (map evocab es)
  PProd p1 p2 -> pvocab p1 `S.union` pvocab p2

psubst :: Var -> Expr -> Prop -> Prop
psubst v e = \case
  PTrue -> PTrue
  PFalse -> PFalse
  PImpl p1 p2 -> PImpl (go p1) (go p2)
  PAnd p1 p2 -> PAnd (go p1) (go p2)
  PNot p -> PNot (go p)
  PEql e1 e2 -> PEql (esubst v e e1) (esubst v e e2)
  PLt e1 e2 -> PLt (esubst v e e1) (esubst v e e2)
  PRel n es -> PRel n (map (esubst v e) es)
  PProd p1 p2 -> PProd (go p1) (go p2)
  where
    go = psubst v e

relSubst :: Map Var Prop -> Prop -> Prop
relSubst m = \case
  PTrue -> PTrue
  PFalse -> PFalse
  PImpl p1 p2 -> PImpl (go p1) (go p2)
  PAnd p1 p2 -> PAnd (go p1) (go p2)
  PNot p -> PNot (go p)
  PEql e1 e2 -> PEql e1 e2
  PLt e1 e2 -> PLt e1 e2
  PRel n es -> M.findWithDefault (PRel n es) n m
  PProd p1 p2 -> PProd (go p1) (go p2)
  where
    go = relSubst m

data Com
  = Skip
  | Assign Var Expr
  | If Prop Com Com
  | Seq Com Com
  | While Prop Com
  | Assert Prop
  | Prod Com Com {- NEW -}
  deriving (Show, Read, Eq, Ord)

data Triple = Triple Prop Com Prop
  deriving (Show, Read, Eq, Ord)

-- | A working proof.
data Proof
  = SKIP
  | ASSIGN
  | IF Prop {- branch precondition -} Proof Proof
  | WHILE Com Prop Proof
  | ASSOC Proof
  | COMM Proof
  | PARTITION Prop {- precondition -} Prop {- midcondition -} Com Com Proof {- small proof -} Proof
  | SPLIT Prop {- P0 -} Prop {- Q0 -} Prop {- P1 -} Prop {- Q1 -} Proof Proof
  | FAIL -- The proof that is trivially invalid.
  | CHOICE Prop {- precondition -} [Proof] -- The proof which is valid if any of its arguments are valid.
  | COVER Com Bool {- memoization of implication -} Prop
  deriving (Show, Read, Eq, Ord)

inductive :: Proof -> Maybe Proof
inductive = \case
  SKIP -> Just SKIP
  ASSIGN -> Just ASSIGN
  IF p pr0 pr1 -> IF p <$> inductive pr0 <*> inductive pr1
  WHILE c inv pr0 -> WHILE c inv <$> inductive pr0
  ASSOC pr0 -> ASSOC <$> inductive pr0
  COMM pr0 -> COMM <$> inductive pr0
  PARTITION p r c0 c1 pr0 pr1 ->
    PARTITION p r c0 c1 <$> inductive pr0 <*> inductive pr1
  SPLIT p0 q0 p1 q1 pr0 pr1 ->
    SPLIT p0 q0 p1 q1 <$> inductive pr0 <*> inductive pr1
  FAIL -> Nothing
  CHOICE p prs -> listToMaybe $ mapMaybe inductive prs
  COVER c b inv -> if b then Just (COVER c b inv) else Nothing

-- | Calculate a covering in the proof: That is, look at the while loop
-- invariants and check if one is covered by a previous version.
cover :: Proof -> Proof
cover p = runReader (cover' p) M.empty

cover' :: Proof -> Reader (Map Com (Set Prop)) Proof
cover' = \case
  SKIP -> pure SKIP
  ASSIGN -> pure ASSIGN
  WHILE c inv proof' -> local (M.insertWith S.union c (S.singleton inv))
    $ WHILE c inv <$> cover' proof'
  COVER c _ inv -> do
    invs <- asks (M.findWithDefault S.empty c)
    let covered = foldr PAnd PTrue invs `implies` inv
    pure $ COVER c covered inv
  ASSOC proof' -> ASSOC <$> cover' proof'
  COMM proof' -> COMM <$> cover' proof'
  PARTITION p r c0 c1 proof' proof'' ->
    PARTITION p r c0 c1 <$> cover' proof' <*> cover' proof''
  SPLIT p0 q0 p1 q1 proof0 proof1 ->
    SPLIT p0 q0 p1 q1 <$> cover' proof0 <*> cover' proof1
  (FAIL) -> pure FAIL
  CHOICE p proofs -> CHOICE p <$> mapM cover' proofs
  _ -> pure FAIL

-- | Replace each relational predicate in the proof by its definition.
populate :: Map Var Prop -> Proof -> Proof
populate m = \case
  SKIP -> SKIP
  ASSIGN -> ASSIGN
  IF p pr0 pr1 -> IF (relSubst m p) (go pr0) (go pr1)
  WHILE c p pr0 -> WHILE c (relSubst m p) (go pr0)
  ASSOC pr0 -> ASSOC (go pr0)
  COMM pr0 -> COMM (go pr0)
  PARTITION p r c0 c1 pr0 pr1 ->
    PARTITION (relSubst m p)
              (relSubst m r)
              c0 c1 (go pr0) (go pr1)
  SPLIT p0 q0 p1 q1 pr0 pr1 ->
    SPLIT (relSubst m p0)
          (relSubst m q0)
          (relSubst m p1)
          (relSubst m q1)
          (go pr0)
          (go pr1)
  FAIL -> FAIL
  CHOICE p prs -> CHOICE (relSubst m p) (map go prs)
  COVER c b p -> COVER c b (relSubst m p)
  where
    go = populate m

replay :: Com -> Proof -> Prop -> WriterT [Prop] (State Int) (Prop, Proof)
replay c proof q =
  case (c, proof) of
    (Skip, SKIP) -> pure (q, SKIP)
    (Assign x e, ASSIGN) -> pure (psubst x e q, ASSIGN)
    (If cond c0 c1 `Prod` c', IF p pr0 pr1) -> do
      (q0, pr0') <- replay (c0 `Prod` c') pr0 q
      (q1, pr1') <- replay (c1 `Prod` c') pr1 q
      clause (PAnd p cond) q0
      clause (PAnd p (PNot cond)) q1
      pure (p, IF p pr0' pr1')
    (While e c0 `Prod` c', WHILE c p pr0) -> undefined
    (c0 `Prod` (c1 `Prod` c2), ASSOC pr0) -> do
      (p, pr0') <- replay ((c0 `Prod` c1) `Prod` c2) pr0 (associateR {- ? -} q)
      pure (associateL {- ? -} p, ASSOC pr0')
    (c0 `Prod` c1, COMM pr0) -> do
      (p, pr0') <- replay (c1 `Prod` c0) pr0 (commute {- ? -} q)
      pure (commute p, COMM pr0')
    (_, PARTITION p r c0 c1 pr0 pr1) -> do
      (p0, pr0') <- replay c0 pr0 r
      (p1, pr1') <- replay (c0 `Prod` c1) pr1 (pairwise r q)
      clause p p0
      clause (pairwise p r) p1
      pure (p, PARTITION p r c0 c1 pr0' pr1')
    (_, SPLIT{}) -> undefined
    (_, FAIL) -> extend c q
    (_, CHOICE p prs) -> do
      prs' <- mapM (\pr -> do
        (p', pr') <- replay c pr q
        clause p p'
        pure pr') prs
      pure (p, CHOICE p prs')
    (_, COVER c _ p) -> pure (p {- ? -}, COVER c False p)

extend :: Com -> Prop -> WriterT [Prop] (State Int) (Prop, Proof)
extend = undefined

solveChc :: [Prop] -> Either (Map Var Prop) (Map Var Prop)
solveChc = undefined

implies :: Prop -> Prop -> Bool
implies = undefined

-- | The core loop. Construct a larger CHC system by replaying the proof,
-- extending it at each underapproximation. Then, solve the CHC system and
-- search for an inductive proof.
loop :: Triple -> Proof -> State Int (Either (Map Var Prop) Proof)
loop (Triple p c q) proof = do
  (proof', chc) <- runWriterT (do
    (p', pr) <- replay c proof q
    clause p p'
    pure pr )
  case solveChc chc of
    -- If there is a counterexample, we are done.
    Left counterexample -> pure (Left counterexample)
    -- Otherwise, we examine the model for inductiveness.
    Right model -> -- Construct a version of the proof where predicates have been
                   -- substituted by their definition. Check if this proof has
                   -- inductive loop invariants.
                   case inductive (cover (populate model proof')) of
                      -- If there is a complete proof, we are done.
                      Just theProof -> pure $ Right theProof
                      -- Otherwise, loop over the larger proof.
                      Nothing -> loop (Triple p c q) proof'

-- | Run the core loop starting from an underapproximation of a potential
-- proof, the proof which is trivially invalid.
proofHound :: Triple -> Either (Map Var Prop) Proof
proofHound triple = evalState (loop triple FAIL) 0

isSimple :: Com -> Bool
isSimple = \case
  While{} -> False
  If _ c0 c1 -> isSimple c0 && isSimple c1
  Seq c0 c1 -> isSimple c0 && isSimple c1
  Prod c0 c1 -> isSimple c0 && isSimple c1
  _ -> True

isSeq :: Com -> Bool
isSeq = \case
  Seq{} -> True
  _ -> False

cvocab :: Com -> Set Var
cvocab = \case
  Skip -> S.empty
  Assign v e -> S.insert v (evocab e)
  If p c1 c2 -> S.unions [pvocab p, cvocab c1, cvocab c2]
  Seq c1 c2 -> cvocab c1 `S.union` cvocab c2
  While p c -> pvocab p `S.union` cvocab c
  Prod c1 c2 -> cvocab c1 `S.union` cvocab c2
  Assert p -> pvocab p

mkRel :: MonadState Integer m => Set Var -> m Prop
mkRel voc = do
  c <- get
  put (c+1)
  pure $ PRel ("$rel" ++ show c) (map V $ S.toList voc)

clause :: MonadWriter [Prop] m => Prop -> Prop -> m ()
clause pre post =
  tell [foldr PForall (PImpl pre post) (pvocab (PAnd pre post))]

partitions :: Com -> [(Com, Com)]
partitions (Seq c0 c1) =
  let ps0 = do
        (c0', c0'') <- if not (isSimple c0 || isSeq c0)
                       then [(c0, Skip)]
                       else partitions c0
        pure (c0', c0'' `Seq` c1)
      ps1 = do
        (c1', c1'') <- if not (isSimple c1 || isSeq c1)
                       then [(Skip, c1)]
                       else partitions c1
        pure (c0 `Seq` c1', c1'')
   in ps0 ++ ps1
partitions (Prod c0 c1) = do
  (c0', c0'') <- partitions c0 ++ [(c0, Skip)]
  (c1', c1'') <- partitions c1 ++ [(c1, Skip)]
  if c0'' == Skip && c1'' == Skip
  then []
  else pure (c0' `Prod` c1', c0'' `Prod` c1'')
partitions _ = []

chunk :: Triple -> StateT Integer (Writer [Prop]) Triple
chunk (Triple p c q) =
  case partitions c of
    [] -> pure (Triple p c q)
    ((c0, c1):_) -> do
       r <- mkRel (S.unions [cvocab c, pvocab p, pvocab q])
       chunk $ Triple (PProd p r) (c0 `Prod` c1) (PProd r q)

part :: Com -> Com
part c
  | isSimple c = c
  | otherwise =
    case c of
      Seq a b ->
        case (assocRight $ part a, assocLeft $ part b) of
          (Prod a0 a1, Prod b0 b1) ->
            if isSimple a1 && isSimple b0
            then Prod a0 (Prod (Seq a1 b0) b1)
            else foldr1 Prod [a0, a1, b0, b1]
          (a0, Prod b0 b1) ->
            if isSimple a0 && isSimple b0
            then Prod (Seq a0 b0) b1
            else foldr1 Prod [a0, b0, b1]
          (Prod a0 a1, b0) ->
            if isSimple a1 && isSimple b0
            then Prod a0 (Seq a1 b0)
            else foldr1 Prod [a0, a1, b0]
          (a0, b0) -> Prod a0 b0
      Prod a b -> Prod (part a) (part b)
      c -> c

assocLeft :: Com -> Com
assocLeft = \case
  Prod c0 c1 ->
    case assocLeft c0 of
      Prod c0' c0'' -> Prod c0' (Prod c0'' c1)
      _ -> Prod c0 c1
  c -> c

assocRight :: Com -> Com
assocRight = \case
  Prod c0 c1 ->
    case assocRight c1 of
      Prod c1' c1'' -> Prod (Prod c0 c1') c1''
      _ -> Prod c0 c1
  c -> c

example :: Com
example =
  Assign "sum0" (Lit 0) `Seq`
  Assign "i" (Lit 0) `Seq`
  While (PLt (V "i") (V "n"))
    ( Assign "sum0" (Add (V "sum0") (V "i")) `Seq`
      Assign "i" (Add (V "i") (Lit 1))
    ) `Seq`
  Assign "sum1" (Lit 0) `Seq`
  Assign "i" (Sub (V "n") (Lit 1)) `Seq`
  While (PLt (Lit 0) (V "i"))
    ( Assign "sum1" (Add (V "sum1") (V "i")) `Seq`
      Assign "i" (Sub (V "i") (Lit 1))
    ) `Seq`
  Assert (PEql (V "sum0") (V "sum1"))

chunk' :: IO ()
chunk' =
  case runWriter (evalStateT (chunk examplet) 0) of
    (Triple p c q, ps) -> putStrLn (showCom c)

examplet :: Triple
examplet = Triple PTrue example PTrue

associateL, associateR :: Prop -> Prop
associateL = undefined
associateR = undefined

commute :: Prop -> Prop
commute = \case
  PProd p q -> PProd q p
  _ -> undefined

pairwise :: Prop -> Prop -> Prop
pairwise = undefined

showCom :: Com -> String
showCom = \case
  Assign x e -> x ++ " := " ++ show e
  Assert p -> "assert " ++ show p
  Seq a b -> showCom a ++ ";\n" ++ showCom b
  Prod a b -> "(" ++ showCom a ++ "\n*\n" ++ showCom b ++ ")"
  While e c -> "while " ++ show e ++ " {\n" ++ showCom c ++ "\n}"
  If e c0 c1 -> "if " ++ show e ++ "{\n" ++ showCom c0 ++ "\n} else {\n" ++ showCom c1 ++ "\n}"
  Skip -> "skip"
