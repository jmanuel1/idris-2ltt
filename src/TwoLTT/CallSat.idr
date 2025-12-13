-- https://github.com/AndrasKovacs/staged/blob/c0cf3a58dcc8919aff7fb21391a860f9e8e7df64/icfp24paper/supplement/agda-opsem/README.agda#L17
module TwoLTT.CallSat

import TwoLTT.Expr
import TwoLTT.Types

%default total

etaExpand : {ty : Ty tv Comp} -> Expr var ty -> Expr var ty
etaExpand {ty = (Fun x {u = Val} y)} e = Lam x (\x => App e (Var x))
etaExpand {ty = (Fun x {u = Comp} y)} e = Lam x (\x => etaExpand (App e (Var x)))
etaExpand {ty = (Newtype tag x)} e = Wrap tag (etaExpand (Unwrap e))

etaExpandCompLets : Expr var ty -> Expr var ty
etaExpandCompLets (LetRec a t u) = LetRec a (\x => etaExpand $ etaExpandCompLets (t x)) (\x => etaExpandCompLets (u x))
etaExpandCompLets (Let {u = Val} a t e) = Let a t (\x => etaExpandCompLets (e x))
etaExpandCompLets (Let {u = Comp} a t e) = Let a (etaExpand $ etaExpandCompLets t) (\x => etaExpandCompLets (e x))
etaExpandCompLets (Absurd x) = Absurd (etaExpandCompLets x)
etaExpandCompLets (Match x f g) = Match (etaExpandCompLets x) (\x => etaExpandCompLets (f x)) (\x => etaExpandCompLets (g x))
etaExpandCompLets (Lam a t) = Lam a (\x => etaExpandCompLets (t x))
etaExpandCompLets e@(Var x) = e
etaExpandCompLets (App f arg) = App (etaExpandCompLets f) (etaExpandCompLets arg)
etaExpandCompLets (Left x) = Left $ etaExpandCompLets x
etaExpandCompLets (Right x) = Right $ (etaExpandCompLets x)
etaExpandCompLets TT = TT
etaExpandCompLets (Prod x y) = Prod (etaExpandCompLets x) (etaExpandCompLets y)
etaExpandCompLets (First x) = First (etaExpandCompLets x)
etaExpandCompLets (Rest x) = Rest $ etaExpandCompLets x
etaExpandCompLets (Wrap tag x) = Wrap tag (etaExpandCompLets x)
etaExpandCompLets (Unwrap x) = Unwrap (etaExpandCompLets x)
etaExpandCompLets (Roll x sub) = Roll (etaExpandCompLets x) sub
etaExpandCompLets (Unroll x sub) = Unroll (etaExpandCompLets x) sub
