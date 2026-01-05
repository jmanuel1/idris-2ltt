module TwoLTT.Monad.Maybe

import Control.Monad.Maybe
import Control.Monad.Trans
import TwoLTT.Expr
import TwoLTT.Gen
import TwoLTT.Maybe
import TwoLTT.Monad.Improve
import TwoLTT.Split
import TwoLTT.Types

%default total

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

export
(i : Improve tv var m) => Improve tv var (MaybeT m) where
  Univ = Univ @{i}
  F = MaybeT (F @{i})
  up x = MkMaybeT $ do
    ma <- up x
    liftGen $ map (map Var) $ splitMaybe _ ma
  down _ (MkMaybeT x) = down _ $ x >>= \case
    Nothing => pure nothing
    Just a => pure (just a)

export
fail : (i : Improve tv var m) => {a : Ty tv Val} -> Expr var (MaybeT (F @{i}) a)
fail = down {m = MaybeT m} a nothing
