module TwoLTT.Monad.Improve

import public TwoLTT.Expr
import public TwoLTT.Gen
import public TwoLTT.Types

-- https://github.com/AndrasKovacs/staged/blob/main/icfp24paper/supplement/haskell-cftt/CFTT/Improve.hs#L17
public export
interface MonadGen Val var m => Improve (0 tyvar : Type) (0 var : VarTy tyvar) (0 m : Type -> Type) | m where
  Univ : U
  F : Ty tyvar Val -> Ty tyvar Univ
  up : {a : Ty tyvar Val} -> Expr var (F a) -> m (Expr var a)
  down : (a : Ty _ Val) -> m (Expr var a) -> Expr var (F a)
