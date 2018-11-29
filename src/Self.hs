module Self where

data Var deriving (Show, Read, Eq, Ord)
data AExpr deriving (Show, Read, Eq, Ord)
data BExpr deriving (Show, Read, Eq, Ord)

data Com
  = Assign Var AExpr
  | Assert BExpr
  | Seq Com Com
  | Sum Com Com
  | Prod Com Com
  | Loop Com
  deriving (Show, Read, Eq, Ord)
