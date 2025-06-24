module TwoLTT.Types.Sub

import Data.Vect
import TwoLTT.Types

%default total

-- http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf, figure 9
public export
data Sub : (0 t1 : var -> Ty var Val) -> Ty var Val -> Ty var Val -> Type where
  [search t1]
  SubFix : (t1 : var -> var -> Ty var Val) -> (forall a. Sub (\a' => t1 a' a) t (t1' a)) -> Sub (\a => Fix (t1 a)) t (Fix t1')
  -- NOTE: Avoid trying to unify against a `map` call by having t2s return the
  -- whole list. The unifier likes this a lot better (see definition of
  -- `TreeExample.leaf`).
  SubSum : Sub t1 t t1' -> (t2s : var -> Vect n (Ty var Val)) -> {0 t2s' : Vect n _} -> Sub (\a => Sum (t2s a)) t (Sum t2s') -> Sub (\a => Sum (t1 a :: t2s a)) t (Sum (t1' :: t2s'))
  SubProd :
    Sub t1 t t1' ->
    (t2s : var -> Vect n (Ty var Val)) ->
    {0 t2s' : Vect n _} ->
    Sub (\a => Product (t2s a)) t (Product t2s') ->
    Sub (\a => Product (t1 a :: t2s a)) t (Product (t1' :: t2s'))
  SubReplace : Sub (\a => TyVar a) t t
  SubConst : Sub (\_ => t1) t t1
  SubNewtype : Sub t1 t t1' -> Sub (\a => Newtype tag (t1 a)) t (Newtype tag t1')

%name Sub sub

export
subFixZeroConst : (sub : Sub f (Fix f) Zero) -> (f === \_ => Zero, sub ~=~ SubConst {t = Fix f, t1 = Zero})
subFixZeroConst SubConst = (Refl, Refl)

--export
--subFixUnroll : (sub : Su)
