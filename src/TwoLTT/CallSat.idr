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

etaExpandNonVariableAppHeads : Expr var ty -> Expr var ty
etaExpandNonVariableAppHeads (App f@(Var _) x) = App f (etaExpandNonVariableAppHeads x)
etaExpandNonVariableAppHeads (App f@(App _ _) x) = App (etaExpandNonVariableAppHeads f) (etaExpandNonVariableAppHeads x)
etaExpandNonVariableAppHeads (App f x) = App (etaExpand $ etaExpandNonVariableAppHeads f) (etaExpandNonVariableAppHeads x)
etaExpandNonVariableAppHeads (LetRec a t u) = LetRec a (\x => etaExpandNonVariableAppHeads (t x)) (\x => etaExpandNonVariableAppHeads $ u x)
etaExpandNonVariableAppHeads (Let a t u) = Let a (etaExpandNonVariableAppHeads t) (\x => (etaExpandNonVariableAppHeads (u x)))
etaExpandNonVariableAppHeads (Absurd x) = Absurd (etaExpandNonVariableAppHeads x)
etaExpandNonVariableAppHeads (Match x f g) = Match (etaExpandNonVariableAppHeads x) (\x => etaExpandNonVariableAppHeads $ f x) (\x => (etaExpandNonVariableAppHeads $ g x))
etaExpandNonVariableAppHeads (Lam a t) = Lam a (\x => etaExpandNonVariableAppHeads $ t x)
etaExpandNonVariableAppHeads e@(Var x) = e
etaExpandNonVariableAppHeads (Left x) = Left (etaExpandNonVariableAppHeads x)
etaExpandNonVariableAppHeads (Right x) = Right (etaExpandNonVariableAppHeads x)
etaExpandNonVariableAppHeads TT = TT
etaExpandNonVariableAppHeads (Prod x y) = Prod (etaExpandNonVariableAppHeads x) (etaExpandNonVariableAppHeads y)
etaExpandNonVariableAppHeads (First x) = First (etaExpandNonVariableAppHeads x)
etaExpandNonVariableAppHeads (Rest x) = Rest (etaExpandNonVariableAppHeads x)
etaExpandNonVariableAppHeads (Wrap tag x) = Wrap tag (etaExpandNonVariableAppHeads x)
etaExpandNonVariableAppHeads (Unwrap x) = Unwrap (etaExpandNonVariableAppHeads x)
etaExpandNonVariableAppHeads (Roll x sub) = Roll (etaExpandNonVariableAppHeads x) sub
etaExpandNonVariableAppHeads (Unroll x sub) = Unroll (etaExpandNonVariableAppHeads x) sub
