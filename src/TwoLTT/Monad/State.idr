module TwoLTT.Monad.State

import Control.Monad.State
import Data.Vect
import TwoLTT.Gen
import TwoLTT.Monad.Improve
import TwoLTT.Types

export
StateT : Ty var Val -> (Ty var Val -> Ty var Val) -> Ty var Val -> Ty var Comp
StateT s m a = Fun s (m (Product [a, s]))

export
MonadGen u var m => MonadGen u var (StateT s m) where
  liftGen = lift . liftGen

export
[improveStateInstance]
{f : Ty tv Val -> Ty tv Val} -> {s : Ty tv Val} -> Improve var f m => Improve var (StateT s f) (StateT (Expr var s) m) where
  up x = ST $ \s => do
    h <- up (App x s)
    pure (First (Rest h), First h)
  down _ x = Lam _ $ \s => down _ $ do
    (s, a) <- runStateT (Var s) x
    pure (Prod a (Prod s TT))
