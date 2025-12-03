module TwoLTT.Gen

import TwoLTT.Expr
import TwoLTT.Types

%default total

public export
record Gen (0 u : U) (0 var : VarTy tv) (a : Type) where
  constructor MkGen
  -- `r` is explicit because of https://github.com/idris-lang/Idris2/issues/3533.
  unGen : (0 r : Ty tv u) -> (a -> Expr var r) -> Expr var r

export
runGen : {0 a : Ty tv u} -> Gen u var (Expr var a) -> Expr var a
runGen gen = unGen gen _ id

export
gen : {v : U} -> {0 a : Ty tv v} -> Expr var a -> Gen u var (Expr var a)
gen e = MkGen $ \_, k => Let _ e (\x => k (Var x))

public export
interface Monad m => MonadGen (0 u : U) (0 var : VarTy tv) m | m where
  liftGen : Gen u var a -> m a

export
Functor (Gen u var) where
  map f fa = MkGen $ \_, k => unGen fa _ $ \fa => k (f fa)

export
Applicative (Gen u var) where
  pure a = MkGen $ \_, k => k a
  fa <*> a = MkGen $ \_, k => unGen fa _ $ \fa => unGen a _ $ \a => k (fa a)

export
Monad (Gen u var) where
  m >>= f = MkGen $ \_, k => unGen m _ (\a => unGen (f a) _ k)

export
MonadGen u var (Gen u var) where
  liftGen gen = gen
