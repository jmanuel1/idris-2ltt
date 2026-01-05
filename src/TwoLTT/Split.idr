module TwoLTT.Split

import TwoLTT.Gen
import public TwoLTT.Expr -- for writing the SplitTo type
import public TwoLTT.Types

public export
0 SplitTy : (SplitTo : VarTy tyvar -> Type) -> Ty tyvar Val -> Type
SplitTy SplitTo@_ a = (0 var : VarTy tyvar) -> Expr var a -> Gen Val var (SplitTo var)
