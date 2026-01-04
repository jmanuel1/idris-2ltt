module TwoLTT.Monad.State

import Data.Vect
import TwoLTT.Types

export
StateT : Ty var Val -> (Ty var Val -> Ty var Val) -> Ty var Val -> Ty var Comp
StateT s m a = Fun s (m (Product [a, s]))
