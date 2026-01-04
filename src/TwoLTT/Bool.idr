module TwoLTT.Bool

import TwoLTT.Expr
import TwoLTT.Gen
import TwoLTT.Split
import TwoLTT.Types

export
Bool : Ty var Val
Bool = Sum [One, One]

export
true : Expr var Bool
true = Left TT

export
false : Expr var Bool
false = Right $ Left TT

export
splitBool : SplitTy (const Bool) Bool
splitBool _ b = MkGen $ \_, k => Case b [\_ => k True, \_ => k False]
