module TwoLTT.Monad.Improve

import public TwoLTT.Expr
import public TwoLTT.Gen
import public TwoLTT.Types

-- https://github.com/AndrasKovacs/staged/blob/main/icfp24paper/supplement/haskell-cftt/CFTT/Improve.hs#L17
public export
interface MonadGen Val var m => Improve (0 var : VarTy tyvar) (0 f : Ty tyvar Val -> Ty tyvar u) (0 m : Type -> Type) | m where
  up : {a : Ty _ Val} -> Expr var (f a) -> m (Expr var a)
  down : (a : Ty _ Val) -> m (Expr var a) -> Expr var (f a)
