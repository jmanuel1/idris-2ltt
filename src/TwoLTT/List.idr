module TwoLTT.List

import Data.Vect
import Data.Vect.Quantifiers
import TwoLTT.Gen
import public TwoLTT.Split
import TwoLTT.Types

export
List : Ty tyvar Val -> Ty tyvar Val
List a = Fix (\list => Sum [One, Product [a, TyVar list]])

export
splitList : {a : Ty tyvar Val} -> SplitTy (\var => Maybe (var _ a, var _ (List a))) (List a)
splitList _ as = MkGen $ \_, k =>
  Case (Unroll as %search) [
    \_ => k Nothing,
    \cons =>
      Let a (First (Var cons)) $ \head =>
      Let (List a) (First (Rest (Var cons))) $ \tail =>
      k (Just (head, tail))
  ]
