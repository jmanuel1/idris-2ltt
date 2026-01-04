module TwoLTT.Split

import TwoLTT.Gen
import TwoLTT.Expr
import public TwoLTT.Types

public export
interface Split (0 a : Ty tyvar Val) where
  0 SplitTo : VarTy tyvar -> Type
  split : (0 var : VarTy _) -> Expr var a -> Gen Val var (SplitTo var)
