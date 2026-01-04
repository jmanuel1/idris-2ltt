module TwoLTT.Maybe

import Data.Vect
import Data.Vect.Quantifiers
import TwoLTT.Expr
import TwoLTT.Split
import TwoLTT.Gen
import TwoLTT.Types

export
Maybe : Ty tyvar Val -> Ty tyvar Val
Maybe a = Sum [One, a]

export
nothing : {0 a : Ty tyvar Val} -> Expr var (Maybe a)
nothing = Left TT

export
just : {0 a : Ty tyvar Val} -> Expr var a -> Expr var (Maybe a)
just a = Right $ Left a

export
{a : Ty tyvar Val} -> Split (Maybe a) where
  SplitTo var = Maybe (Expr var a)
  split _ ma = MkGen $ \_, k => Case ma [\_ => k Nothing, \a => k (Just (Var a))]
