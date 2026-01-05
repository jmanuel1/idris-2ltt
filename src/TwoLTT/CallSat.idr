-- https://github.com/AndrasKovacs/staged/blob/c0cf3a58dcc8919aff7fb21391a860f9e8e7df64/icfp24paper/supplement/agda-opsem/README.agda#L17
module TwoLTT.CallSat

import Data.DPair
import Debug.Trace
import TwoLTT.Expr
import TwoLTT.Types

%default total

etaExpandRec : {u : U} -> {ty : Ty tv u} -> Expr var ty -> Expr var ty
etaExpand' : {u : U} -> {ty : Ty tv u} -> Expr var ty -> Expr var ty
etaExpand : {ty : Ty tv Comp} -> Expr var ty -> Expr var ty

etaExpand {ty = (Fun x {u = Comp} y)} (Lam x e) = Lam x (\x => etaExpand (e x))
etaExpand {ty = (Fun x y)} f@(Lam x e) = f
etaExpand {ty = (Fun x {u = Comp} y)} e = Lam x (\x => etaExpand (App e (Var x)))
etaExpand {ty = (Fun x y)} e = Lam x (\x => (App e (Var x)))

etaExpand' {u = Comp} e = etaExpand $ etaExpandRec e
etaExpand' {u = Val} e = etaExpandRec e

etaExpandRec (Lam x e) = Lam x (\x => etaExpand' (e x))
etaExpandRec (LetRec a t f) = LetRec a (\x => etaExpand' (t x)) (\x => etaExpand' (f x))
etaExpandRec (Let a t f) = Let a (etaExpand' (t)) (\x => etaExpand' (f x))
etaExpandRec (Absurd x) = Absurd (etaExpandRec x)
etaExpandRec (Match x f g) = Match (etaExpandRec x) (\x => etaExpand' (f x)) (\x => etaExpand' (g x))
etaExpandRec e@(Var x) = e
etaExpandRec (App f arg) = App (etaExpand' f) (etaExpand' arg)
etaExpandRec (Left x) = Left (etaExpandRec x)
etaExpandRec (Right x) = Right (etaExpandRec x)
etaExpandRec TT = TT
etaExpandRec (Prod x y) = Prod (etaExpandRec x) (etaExpandRec y)
etaExpandRec (First x) = First (etaExpandRec x)
etaExpandRec (Rest x) = Rest (etaExpandRec x)
etaExpandRec (Roll x sub) = Roll (etaExpandRec x) sub
etaExpandRec (Unroll x sub) = Unroll (etaExpandRec x) sub

etaExpandCompLets : Expr var ty -> Expr var ty
etaExpandCompLets (LetRec a t u) = LetRec a (\x => etaExpand' $ etaExpandCompLets (t x)) (\x => etaExpandCompLets (u x))
etaExpandCompLets (Let {u = Val} a t e) = Let a (etaExpandCompLets t) (\x => etaExpandCompLets (e x))
etaExpandCompLets (Let {u = Comp} a t e) = Let a (etaExpand' $ etaExpandCompLets t) (\x => etaExpandCompLets (e x))
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
etaExpandCompLets (Roll x sub) = Roll (etaExpandCompLets x) sub
etaExpandCompLets (Unroll x sub) = Unroll (etaExpandCompLets x) sub

etaExpandNonVariableAppHeads : {u : U} -> {0 ty : Ty tv u} -> Expr var ty -> Expr var ty
etaExpandNonVariableAppHeads (App f@(Var _) x) = App f (etaExpandNonVariableAppHeads x)
etaExpandNonVariableAppHeads (App f@(App _ _) x) = App (etaExpandNonVariableAppHeads f) (etaExpandNonVariableAppHeads x)
etaExpandNonVariableAppHeads (App f x) = App (etaExpand' $ etaExpandNonVariableAppHeads f) (etaExpandNonVariableAppHeads x)
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
etaExpandNonVariableAppHeads (Roll x sub) = Roll (etaExpandNonVariableAppHeads x) sub
etaExpandNonVariableAppHeads (Unroll x sub) = Unroll (etaExpandNonVariableAppHeads x) sub

||| Bring computational eliminators deeper into binders.
deepenElims : {u : U} -> {0 a : Ty tv u} -> Expr var a -> Expr var a
deepenElims (LetRec x t u) = (LetRec x (\x => (deepenElims $ t x)) (\x => deepenElims $ u x))
deepenElims (Let x t u) = (Let x (deepenElims t) $ \x => (deepenElims $ u x))
deepenElims (Absurd x) = (Absurd (deepenElims x))
deepenElims (Match x f g) = (Match (deepenElims x) (\x => (deepenElims $ f x)) $ \x => (deepenElims $ g x))
deepenElims (Lam x t) = (Lam x $ \x => (deepenElims $ t x))
deepenElims e@(Var x) = e
deepenElims (App (LetRec x t u) arg@(Var _)) = LetRec x (\x => deepenElims $ t x) (\x => deepenElims $ App (u x) arg)
deepenElims (App (Let x t u) arg@(Var _)) = Let x (deepenElims t) (\x => deepenElims $ App (u x) arg)
deepenElims (App (Match x f g) arg@(Var _)) = Match (deepenElims x) (\x => deepenElims $ App (f x) arg) (\x => deepenElims $ App (g x) arg)
deepenElims (App (Lam a t) (Var arg)) = deepenElims $ t arg
deepenElims (App f arg@(Var _)) = App (deepenElims f) arg
deepenElims (App f arg) = Let _ (deepenElims arg) $ \x => App (deepenElims f) $ Var x
deepenElims (Left x) = Left $ deepenElims x
deepenElims (Right x) = Right $ deepenElims x
deepenElims TT = TT
deepenElims (Prod x y) = Prod (deepenElims x) (deepenElims y)
deepenElims (First x) = First $ deepenElims x
deepenElims (Rest x) = Rest $ deepenElims x
deepenElims (Roll x sub) = Roll (deepenElims x) sub
deepenElims (Unroll x sub) = Unroll (deepenElims x) sub

covering
fixpoint : {0 a : Ty tv u} -> ({0 var : VarTy tv} -> Expr var a -> Expr var a) -> ({0 var : VarTy tv} -> Expr var a) -> Expr var a
fixpoint f e =
  let toStr : ((0 var : VarTy tv) -> Expr var a) -> String := \e => toStringWithoutTypes 0 (e _)
      e' : (0 var : VarTy tv) -> Expr var a := ({-traceValBy toStr $-} (\_ => f e))
      e'' : {0 var : VarTy tv} -> Expr var a := e' _ in
  if equal 0 e e'' then e'' else fixpoint f e''

export covering
saturateCalls : {u : U} -> {a : Ty tv u} -> Expr' a -> Expr var a
saturateCalls e =
  let e' : Expr' a := e |> etaExpandCompLets |> etaExpandNonVariableAppHeads in
  fixpoint deepenElims e'

public export
ArbExpr : Type -> Type
ArbExpr v = Exists $ \u => Exists $ \tv => Exists (Expr {u, tv} (\_, _ => v))

public export
data CallSatErr v = NotEtaLong (ArbExpr v) | NotSatCall (ArbExpr v)

public export
CallSatResult : Type -> Type
CallSatResult v = Either (CallSatErr v) ()

||| For all computational subterms, test that constructors are on the outside.
isEtaLong : Monoid v => {u : U} -> {0 a : Ty tv u} -> Expr (\_, _ => v) a -> (CallSatResult v)
isEtaLong {u = Val} (LetRec x t u) = isEtaLong (t neutral) >> isEtaLong (u neutral)
isEtaLong {u = Val} (Let x t u) = isEtaLong t >> isEtaLong (u neutral)
isEtaLong {u = Val} (Absurd x) = isEtaLong x
isEtaLong {u = Val} (Match x f g) = isEtaLong x >> isEtaLong (f neutral) >> isEtaLong (g neutral)
isEtaLong {u = Val} (Var x) = Right ()
-- spine of computation eliminator
isEtaLong {u = Val} (App f arg) = {-isEtaLong f >>-} isEtaLong arg
isEtaLong {u = Val} (Left x) = isEtaLong x
isEtaLong {u = Val} (Right x) = isEtaLong x
isEtaLong {u = Val} TT = Right ()
isEtaLong {u = Val} (Prod x y) = isEtaLong x >> isEtaLong y
isEtaLong {u = Val} (First x) = isEtaLong x
isEtaLong {u = Val} (Rest x) = isEtaLong x
isEtaLong {u = Val} (Roll x sub) = isEtaLong x
isEtaLong {u = Val} (Unroll x sub) = isEtaLong x
isEtaLong {u = Comp} (Lam x t) = isEtaLong (t neutral)
isEtaLong {u = Comp} e = Left (NotEtaLong (Evidence _ (Evidence _ (Evidence _ e))))

export
areCallsSaturated : Monoid v => {u : U} -> {0 a : Ty tv u} -> Expr (\_, _ => v) a -> CallSatResult v
areCallsSaturated e@(LetRec x t u) =
  isEtaLong (t neutral) >> areCallsSaturated (t neutral) >> areCallsSaturated (u neutral)
areCallsSaturated e@(Let {u = Comp} x t u) =
  isEtaLong t >> areCallsSaturated t >> areCallsSaturated (u neutral)
areCallsSaturated e@(Let {u = _} x t u) =
  areCallsSaturated t >> areCallsSaturated (u neutral)
areCallsSaturated (Absurd x) = areCallsSaturated x
areCallsSaturated (Match x f g) = areCallsSaturated x >> areCallsSaturated (f neutral) >> areCallsSaturated (g neutral)
areCallsSaturated (Lam x t) = areCallsSaturated (t neutral)
areCallsSaturated (Var x) = Right ()
areCallsSaturated (App (Var f) arg) = areCallsSaturated arg
areCallsSaturated (App f@(App _ _) arg) = areCallsSaturated f >> areCallsSaturated arg
areCallsSaturated e@(App f arg) = Left (NotSatCall $ Evidence _ (Evidence _ (Evidence _ e)))
areCallsSaturated (Left x) = areCallsSaturated x
areCallsSaturated (Right x) = areCallsSaturated x
areCallsSaturated TT = Right ()
areCallsSaturated (Prod x y) = areCallsSaturated x >> areCallsSaturated y
areCallsSaturated (First x) = areCallsSaturated x
areCallsSaturated (Rest x) = areCallsSaturated x
areCallsSaturated (Roll x sub) = areCallsSaturated x
areCallsSaturated (Unroll x sub) = areCallsSaturated x
