module TwoLTT.Monad.Maybe

import Control.Monad.Maybe
import Control.Monad.Trans
import TwoLTT.Expr
import TwoLTT.Gen
import TwoLTT.Maybe
import TwoLTT.Monad.Improve
import TwoLTT.Split
import TwoLTT.Types

export
MaybeT : (Ty var Val -> Ty var u) -> Ty var Val -> Ty var u
MaybeT m a = m (Maybe a)

export
runMaybeT : {0 m : Ty tv Val -> Ty tv u} -> {0 a : Ty tv Val} -> Expr var (MaybeT m a) -> Expr var (m (Maybe a))
runMaybeT = id

export
MkMaybeT : {0 m : Ty tv Val -> Ty tv u} -> {0 a : Ty tv Val} -> Expr var (m (Maybe a)) -> Expr var (MaybeT m a)
MkMaybeT = id

export
MonadGen u var m => MonadGen u var (MaybeT m) where
  liftGen = lift . liftGen

-- NOTE: For some reason, auto search can't find this, and it's rather
-- annoying.
export
[improveMaybeInstance]
{0 f : Ty tv Val -> Ty tv u} -> Improve var f m => Improve var (MaybeT f) (MaybeT m) where
  up x = MkMaybeT $ do
    ma <- up $ runMaybeT {m = f} x
    liftGen $ map (map Var) $ splitMaybe _ ma
  down _ (MkMaybeT x) = MkMaybeT {m = f} $ down _ $ x >>= \case
    Nothing => pure nothing
    Just a => pure (just a)

export
fail : {0 f : Ty tv Val -> Ty tv u} -> Improve var f m => {a : Ty tv Val} -> Expr var (MaybeT f a)
fail = down _ @{improveMaybeInstance} {m = MaybeT m} nothing
