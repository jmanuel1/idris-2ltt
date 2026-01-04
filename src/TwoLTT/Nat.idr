module TwoLTT.Nat

import TwoLTT.Expr
import TwoLTT.Gen
import public TwoLTT.Split
import TwoLTT.Types

export
Nat : Ty tyVar Val
Nat = Fix (\nat => Sum [One, TyVar nat])

export
splitNat : SplitTy (\var => Maybe (var _ Nat)) Nat
splitNat _ n = MkGen $ \_, k => Case (Unroll n %search) [\_ => k Nothing, \n' => k (Just n')]

export
fromInteger : (n : Integer) -> Expr v Nat
fromInteger n = if n <= 0 then Roll (Left TT) %search else Roll (Right $ Left $ assert_total $ fromInteger (n - 1)) %search
