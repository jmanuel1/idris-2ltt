module TwoLTT.Tree

import Data.Vect
import Data.Vect.Quantifiers
import TwoLTT.Expr
import TwoLTT.Gen
import public TwoLTT.Split
import TwoLTT.Types

export
TreeF : Ty tyvar Val -> tyvar -> Ty tyvar Val
TreeF a = (\tree => Sum [One, Product [a, TyVar tree, TyVar tree]])

export
Tree : Ty tyvar Val -> Ty tyvar Val
Tree a = Fix $ TreeF a

export
leaf : {a : Ty tyvar Val} -> Expr var (Tree a)
leaf = Roll (Left TT) %search

export
node : {a : Ty tyvar Val} -> Expr var a -> (l, r : Expr var (Tree a)) -> Expr var (Tree a)
node n l r =
  Roll (Right $ Left $ Prod n (Prod l $ Prod r TT)) %search

public export
data TreeSplit : (0 var : VarTy tyvar) -> Ty tyvar Val -> Type where
  Leaf : {0 a : Ty tyvar Val} -> TreeSplit var a
  Node : {0 var : VarTy tv} -> var _ a -> (l, r : var _ (Tree a)) -> TreeSplit var a

export
splitTree : {a : Ty tyvar Val} -> SplitTy (\var => TreeSplit var a) (Tree a)
splitTree _ as = MkGen $ \_, k =>
  Case (Unroll as %search) [
    \_ => k Leaf,
    \node =>
      Let a (First (Var node)) $ \n =>
      Let (Tree a) (First (Rest (Var node))) $ \l =>
      Let (Tree a) (First (Rest (Rest (Var node)))) $ \r =>
      k (Node n l r)
  ]
