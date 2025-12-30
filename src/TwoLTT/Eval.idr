module TwoLTT.Eval

import Control.Function.FunExt.Axiom
import Control.Relation
import Data.DPair
import Data.Singleton
import Data.Vect.Quantifiers
import TwoLTT.Expr
import TwoLTT.Types

%default total

covering
record Fix (f : Type -> Type) where
  constructor Roll
  unroll : f (Fix f)

covering
0 interpCompTy : Ty Type Comp -> ((n : Nat ** Vect (S n) Type), Type)

covering
0 interpProductTy, interpSumTy : Vect n (Ty Type Val) -> Type

covering
0 InterpValTy : Ty Type Val -> Type
InterpValTy (Fix f) = Fix (\t => (InterpValTy (f t)))
InterpValTy (Product ds) = interpProductTy ds
InterpValTy (Sum ds) = interpSumTy ds
InterpValTy (TyVar x) = x
InterpValTy (Newtype tag x) = (InterpValTy x)

interpProductTy [] = ()
interpProductTy (t :: ts) = ((InterpValTy t), interpProductTy ts)

interpSumTy [] = Void
interpSumTy (t :: ts) = Either (InterpValTy t) (interpSumTy ts)

covering
0 interpTy : {u : U} -> Ty Type u -> Type
interpTy {u = Comp} = (\p => HVect (snd $ fst p) -> snd p) . interpCompTy
interpTy {u = Val} = InterpValTy

-- make sure to eta-expand fix so it can actually terminate
covering
fix : ((a -> b) -> (a -> b)) -> (a -> b)
fix f x = f (fix f) x

interpCompTy (Fun arg {u = Comp} ret) =
  ((_ ** interpTy arg :: snd (fst $ interpCompTy ret)), snd $ interpCompTy ret)
interpCompTy (Fun arg {u = Val} ret) = ((_ ** [interpTy arg]), InterpValTy ret)
interpCompTy (Newtype _ ty) = interpCompTy ty

covering
0 subInterpTy : Sub f s ty -> (InterpValTy (f (InterpValTy s))) === (InterpValTy ty)
subInterpTy (SubFix t1 g) =
  cong Fix $
  funExt $ \t =>
  subInterpTy (g t)
subInterpTy (SubSum sub t2s sub1) =
  let prf = (subInterpTy sub)
      prf1 = (subInterpTy sub1)
  in cong2 Either prf prf1
subInterpTy (SubProd sub t2s sub1) = cong2 (,) (subInterpTy sub) (subInterpTy sub1)
subInterpTy SubReplace = Refl
subInterpTy SubConst = Refl
subInterpTy (SubNewtype sub) = (subInterpTy sub)

covering
eval : {u : U} -> {0 ty : Ty Type u} -> Expr (\u, ty => interpTy ty) ty -> (interpTy ty)

covering
evalComp : {0 ty : Ty Type Comp} -> Expr (\u, ty => interpTy ty) ty -> (interpTy ty)

covering
evalVal : {0 ty : Ty Type Val} -> Expr (\u, ty => interpTy ty) ty -> (interpTy ty)

covering
Uninhabited (Expr (\u, ty => interpTy ty) (Sum [])) where
  uninhabited (LetRec a t u) =
    let t' = fix (\x => evalComp (t x))
    in absurd (u t')
  uninhabited (Let a t u) =
    let t' = eval t
    in absurd (u t')
  uninhabited (Absurd x) = absurd x
  uninhabited (Match {ds = d :: ds} x f g) =
    let x' = evalVal x
    in (either (absurd . f) (absurd . g) x')
  uninhabited (Var x) =
    absurd x
  uninhabited (App f arg) = absurd (evalComp f [eval arg])
  uninhabited (First x) = absurd (fst $ evalVal x)
  uninhabited (Unwrap x) = absurd (evalVal x)
  uninhabited (Unroll {f} x sub) =
    let x' = unroll $ evalVal x
    in void $
    case subFixZeroConst sub of
      (prf, _) => absurd $ replace {p = \f => interpTy (f (Fix (\t => interpTy (f t))))} prf x'

evalVal (LetRec a t u) =
  let t' = fix (\x => evalComp (t x))
  in evalVal (u t')
evalVal (Let a t u) =
  let t' = eval t
  in evalVal (u t')
evalVal (Absurd x) = absurd x
evalVal (Match {ds = d :: ds} x f g) =
  either (evalVal . f) (evalVal . g) $ evalVal x
evalVal (Var x) = x
evalVal (App f arg) =
  let f' = evalComp f
  in f' [evalVal arg]
evalVal (Left x) = Left $ evalVal x
evalVal (Right x) = Right $ evalVal x
evalVal TT = ()
evalVal (Prod x y) = (evalVal x, evalVal y)
evalVal (First x) = fst (evalVal x)
evalVal (Rest x) = snd (evalVal x)
evalVal (Wrap tag x) = evalVal x
evalVal (Unwrap x) = evalVal x
evalVal (Roll x sub) = Roll $ rewrite subInterpTy sub in evalVal x
evalVal (Unroll x sub) =
  let x' = unroll $ evalVal x
  in rewrite sym (subInterpTy sub) in x'

eval {u = Val} = evalVal
eval {u = Comp} = evalComp

evalComp (LetRec a t u) arg =
  let t' = fix (\x => evalComp (t x))
      u' = evalComp (u t')
  in u' arg
evalComp (Let a t u) arg =
  let t' = eval t
  in evalComp (u t') arg
evalComp (Absurd x) arg = absurd x
evalComp (Match {ds = d :: ds} x f g) arg = (either (evalComp . f) (evalComp . g) $ evalVal x) arg
evalComp (Lam a {u = Val} t) (arg :: []) = evalVal (t arg)
evalComp (Lam a {u = Comp} t) (arg :: args) = evalComp (t arg) args
evalComp (Var x) arg = x arg
evalComp (App f x) arg = evalComp f (evalVal x :: arg)
evalComp (Wrap tag x) arg = evalComp x arg
evalComp (Unwrap x) arg = evalComp x arg
