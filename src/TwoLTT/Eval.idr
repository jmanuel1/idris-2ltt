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
0 interpValTy : Ty Type Val -> Type
interpValTy (Fix f) = Fix (\t => (interpValTy (f t)))
interpValTy (Product ds) = HVect $ map interpValTy ds
interpValTy (Sum ds) = Any id $ map interpValTy ds
interpValTy (TyVar x) = x
interpValTy (Newtype tag x) = (interpValTy x)

covering
0 interpTy : {u : U} -> Ty Type u -> Type
interpTy {u = Comp} = (\p => HVect (snd $ fst p) -> snd p) . interpCompTy
interpTy {u = Val} = interpValTy


{-
--apply : {0 a : Ty' Val} -> {0 b : Ty' u} -> Expr (\u, ty => interpTy ty) (Fun a b) -> (interpTy a) -> (interpTy b)
-}
covering
fix : (a -> a) -> a
fix f = f (fix f)

interpCompTy (Fun arg {u = Comp} ret) =
  ((_ ** interpTy arg :: snd (fst $ interpCompTy ret)), snd $ interpCompTy ret)
interpCompTy (Fun arg {u = Val} ret) = ((_ ** [interpTy arg]), interpValTy ret)
interpCompTy (Newtype _ ty) = interpCompTy ty

elimAny : (f (head xs) -> a) -> (Any f (tail xs) -> a) -> Any f xs -> a
elimAny elimHead _ (Here x) = elimHead x
elimAny _ elimTail (There x) = elimTail x

0 funExt : ((x : a) -> f x = g x) -> f = g
funExt _ = believe_me (Refl {x = f})

{-data Zonk : Rel (Ty Type Val) where
  Same : Zonk t t
  Left : Zonk (TyVar t) t
  Right : Zonk t (TyVar t)
-}

-- I don't use Biinjective interface because Any has an erased argument
biinjAny : Any f xs = Any g ys -> (f = g, xs = ys)
biinjAny Refl = (Refl, Refl)

Injective HVect where
  injective Refl = Refl

covering
0 subFixInterp : {unroll : Ty Type Val} -> Sub f (Fix g) unroll -> interpValTy unroll === interpValTy (f (Fix (\t => (interpValTy (g t)))))
subFixInterp (SubFix t1 sub) =
  cong Fix $ funExt $ \t => subFixInterp sub
subFixInterp (SubSum x {n} t2s y) =
  let t1Prf = (subFixInterp x)
      t2Prf : Any id ? === Any id ? := (subFixInterp y)
  in cong (Any id) $ cong2 (::) t1Prf $ snd $ biinjAny t2Prf
subFixInterp (SubProd x t2s y) =
  let t1Prf = (subFixInterp x)
      t2Prf = (subFixInterp y)
  in cong HVect $ cong2 (::) t1Prf $ inj _ t2Prf
subFixInterp SubReplace = Refl
subFixInterp SubConst = Refl
subFixInterp (SubNewtype x) = (subFixInterp x)

0 headMap : (xs : Vect (S n) a) -> head (map f xs) === f (head xs)
headMap (x :: xs) = Refl

0 tailMap : (xs : Vect (S n) a) -> tail (map f xs) === map f (tail xs)
tailMap (x :: xs) = Refl

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
  uninhabited (Match {ds} x f g) =
    let x' = evalVal x
    in elimAny (\l => absurd $ f $ replace {p = id} (headMap {f = interpValTy} ds) l) (\r => absurd $ g $ replace {p = Any id} (tailMap {f = interpValTy} ds) r) x'
  uninhabited (Var x) =
    absurd x
  uninhabited (App f arg) = absurd (evalComp f [eval arg])
  uninhabited (First x) = absurd (head $ evalVal x)
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
evalVal (Match x f g) = ?evalVal_rhs_3
evalVal (Var x) = ?evalVal_rhs_4
evalVal (App f arg) = ?evalVal_rhs_5
evalVal (Left x) = ?evalVal_rhs_6
evalVal (Right x) = ?evalVal_rhs_7
evalVal TT = ?evalVal_rhs_8
evalVal (Prod x y) = ?evalVal_rhs_9
evalVal (First x) = head (evalVal x)
evalVal (Rest x) = tail (evalVal x)
evalVal (Wrap tag x) = evalVal x
evalVal (Unwrap x) = evalVal x
evalVal (Roll x sub) = Roll ?evalVal_rhs_16
evalVal (Unroll x sub) = ?evalVal_rhs_15

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
