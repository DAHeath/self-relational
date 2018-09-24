{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
module Lib where

import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.Except
import           Control.Monad.Writer
import qualified Data.Map as Map
import           Data.Map (Map)

type Var = String
data Expr = Expr
  deriving (Show, Read, Eq, Ord)

data St
  = Singleton (Map Var ([Var], [Var], Com))
  | Composite St St
  deriving (Show, Read, Eq, Ord)

data Com
  = Skip
  | Assign Var Expr
  | If Expr Com Com
  | Seq Com Com
  | Prod Com Com
  | Call [Var] [Expr] Var
  deriving (Show, Read, Eq, Ord)

data Prop
  = PTrue
  | PFalse
  | PImpl Prop Prop
  | PAnd Prop Prop
  | PNot Prop
  deriving (Show, Read, Eq, Ord)

subst :: Var -> Prop -> Prop -> Prop
subst = undefined

partitions :: Com -> [(Com, Com)]
partitions = \case
  c0 `Prod` c1 -> [ (c0' `Prod` c1', c0'' `Prod` c1'')
                  | (c0', c0'') <- partitions c0
                  , (c1', c1'') <- partitions c1
                  ]
  c0 `Seq` c1 -> concat [ [(c0, c1)]
                        , [(c0', c0'' `Seq` c1) | (c0', c0'') <- partitions c0]
                        , [(c0 `Seq` c1', c1'') | (c1', c1'') <- partitions c1]
                        ]
  c -> [(c, Skip), (Skip, c)]

-- | Skip serves as the identity element for both Products and Sequences, so we
-- can safely remove all occurrences.
trim :: Com -> Com
trim = \case
  Skip `Prod` c -> c
  c `Prod` Skip -> c
  c0 `Prod` c1 -> trim c0 `Prod` trim c1
  Skip `Seq` c -> c
  c `Seq` Skip -> c
  c0 `Seq` c1 -> trim c0 `Seq` trim c1
  c -> c

type PS = (Com, Prop)

emit :: Prop -> IO ()
emit = undefined

mkRel = undefined

toProp = undefined

-- | Model constructs CHCs that model the effects of simple subcommands on the
-- left of the command.
model :: Com -> Prop -> IO Prop
model (Assign x e) q = pure (subst x (toProp e) q)
model (If e c0 c1 `Prod` c2) q = do
  p <- mkRel
  q0 <- model (c0 `Prod` c2) q
  q1 <- model (c1 `Prod` c2) q
  emit (PAnd (toProp e) p `PImpl` q0)
  emit (PAnd (PNot $ toProp e) p `PImpl` q1)
  pure p
