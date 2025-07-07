module TwoLTT.Eval

import Control.Function
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
0 interpCompTy : Ty Type Comp -> ((n : Nat ** Vect n Type), Type)

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


{-
--apply : {0 a : Ty' Val} -> {0 b : Ty' u} -> Expr (\u, ty => interpTy ty) (Fun a b) -> (interpTy a) -> (interpTy b)
-}
covering
fix : (a -> a) -> a
fix f = f (fix f)

interpCompTy (Fun arg {u = Comp} ret) =
  ((_ ** interpTy arg :: snd (fst $ interpCompTy ret)), snd $ interpCompTy ret)
interpCompTy (Fun arg {u = Val} ret) = ((_ ** [interpTy arg]), InterpValTy ret)
interpCompTy (Newtype _ ty) = interpCompTy ty

0 funExt : ((x : a) -> f x = g x) -> f = g
funExt _ = believe_me (Refl {x = f})

covering
0 subInterpTy : Sub f s ty -> (InterpValTy (f (InterpValTy s))) === (InterpValTy ty)
subInterpTy (SubFix t1 g) =
  cong Fix $
  funExt $ \t =>
  subInterpTy g
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
evalVal TT = ?evalVal_rhs_8
evalVal (Prod x y) = ?evalVal_rhs_9
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
evalComp (Match x f g) arg = ?ghjg_3
evalComp (Lam a t) arg = ?ghjg_4
evalComp (Var x) arg = ?ghjg_5
evalComp (App f x) arg = ?ghjg_6
evalComp (Wrap tag x) arg = ?ghjg_7
evalComp (Unwrap x) arg = ?ghjg_8
