module TwoLTT.Monad.Identity

import TwoLTT.Gen
import TwoLTT.Monad.Improve
import TwoLTT.Types

export
Identity : Ty tyvar Val -> Ty tyvar Val
Identity a = a

export
Improve tv var (Gen Val var) where
  Univ = Val
  F = Identity
  up x = pure x
  down a x = unGen x _ id
