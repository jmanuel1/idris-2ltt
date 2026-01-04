module TwoLTT.Monad.Identity

import TwoLTT.Gen
import TwoLTT.Monad.Improve
import TwoLTT.Types

export
Identity : Ty tyvar Val -> Ty tyvar Val
Identity a = a

export
Improve var Identity (Gen Val var) where
  up x = pure x
  down a x = unGen x _ id
