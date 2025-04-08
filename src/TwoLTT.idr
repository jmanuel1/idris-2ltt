||| https://andraskovacs.github.io/pdfs/2ltt_icfp24.pdf
||| https://github.com/AndrasKovacs/staged/blob/main/icfp24paper/supplement/agda-opsem/Interpreter.agda
module TwoLTT

import Control.Function
import Control.Monad.Maybe
import Control.Monad.Reader
import Control.Monad.State
import Data.Either
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Nat
import Data.SOP
import Data.Vect
import Data.Vect.Elem
import Syntax.WithProof

%default total

%hide Data.SOP.SOP.SOP

data U = Val | Comp

data Ty : Type -> U -> Type

ValTy : Type -> Type
ValTy var = Ty var Val

CompTy : Type -> Type
CompTy var = Ty var Comp

data Ty where
  Fun : Ty var Val -> Ty var u -> CompTy var
  Fix : (var -> Ty var Val) -> ValTy var
  Product, Sum : (ds : List $ Ty var Val) -> ValTy var
  -- Only used for recursive ValTys, so supporting only ValTy variables is fine
  TyVar : var -> Ty var Val
  Newtype : (0 tag : Type) -> Ty var u -> Ty var u

One, Zero : ValTy var
One = Product []
Zero = Sum []

0 VarTy : Type -> Type
VarTy tyvar = (0 u : U) -> Ty tyvar u -> Type

data Expr : (0 tyvar : Type) -> VarTy tyvar -> Ty tyvar u -> Type

0 CaseArms : List (Ty tyvar Val) -> VarTy tyvar -> Ty tyvar Val -> List Type
CaseArms ds var mot = map (\d => var _ d -> Expr tyvar var mot) ds

-- http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf, figure 9
data Sub : (0 t1 : var -> Ty var Val) -> ValTy var -> ValTy var -> Type where
  [search t1]
  SubFix : (t1 : var -> var -> ValTy var) -> (forall a. Sub (\a' => t1 a' a) t (t1' a)) -> Sub (\a => Fix (t1 a)) t (Fix t1')
  -- NOTE: Avoid trying to unify against a `map` call by having t2s return the
  -- whole list. The unifier likes this a lot better (see definition of
  -- `TreeExample.leaf`).
  SubSum : Sub t1 t t1' -> (t2s : var -> List (ValTy var)) -> Sub (\a => Sum (t2s a)) t (Sum t2s') -> Sub (\a => Sum (t1 a :: t2s a)) t (Sum (t1' :: t2s'))
  SubProd : Sub t1 t t1' -> (t2s : var -> List (ValTy var)) -> Sub (\a => Product (t2s a)) t (Product t2s') -> Sub (\a => Product (t1 a :: t2s a)) t (Product (t1' :: t2s'))
  SubReplace : Sub (\a => TyVar a) t t
  SubConst : Sub (\_ => t1) t t1
  SubNewtype : Sub t1 t t1' -> Sub (\a => Newtype tag (t1 a)) t (Newtype tag t1')

-- http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf
data Expr where
  LetRec : {0 var : VarTy tyvar} -> (a : CompTy tyvar) -> (t : var _ a -> Expr tyvar var a) -> (u : var _ a -> Expr tyvar var ty) -> Expr tyvar var ty
  Let : {0 var : VarTy tyvar} -> (a : Ty tyvar u) -> (t : Expr tyvar var a) -> (u : var _ a -> Expr tyvar var ty) -> Expr tyvar var ty
  -- Not having multi-way case in syntax so that Idris can see totality of Expr
  Absurd : Expr tyvar var Zero -> Expr tyvar var a
  Match : Expr tyvar var (Sum (d :: ds)) -> (var _ d -> Expr tyvar var a) -> (var _ (Sum ds) -> Expr tyvar var a) -> Expr tyvar var a
  Lam : {0 var : VarTy tyvar} -> (a : ValTy tyvar) -> (t : var _ a -> Expr tyvar var b) -> Expr {u = Comp} tyvar var (Fun a b)
  Var : {0 var : VarTy tyvar} -> var _ ty -> Expr tyvar var ty
  App : (f : Expr tyvar var (Fun a b)) -> (arg : Expr tyvar var a) -> Expr tyvar var b
  Left : {0 var : VarTy tyvar} -> Expr tyvar var a -> Expr tyvar var (Sum (a :: b))
  Right : {0 var : VarTy tyvar} -> Expr tyvar var (Sum b) -> Expr tyvar var (Sum (a :: b))
  TT : Expr tyvar var One
  Prod : Expr tyvar var a -> Expr tyvar var (Product b) -> Expr tyvar var (Product (a :: b))
  First : Expr tyvar var (Product (a :: as)) -> Expr tyvar var a
  Rest : Expr tyvar var (Product (a :: as)) -> Expr tyvar var (Product as)
  -- Represent coercions explicitly in syntax
  Wrap : (0 tag : Type) -> Expr tyvar var a -> Expr tyvar var (Newtype tag a)
  Unwrap : Expr tyvar var (Newtype tag a) -> Expr tyvar var a
  Roll : Expr tyvar var unroll -> (0 sub : Sub f (Fix f) unroll) -> Expr tyvar var (Fix f)
  Unroll : Expr tyvar var (Fix f) -> (0 sub : Sub f (Fix f) unroll) -> Expr tyvar var unroll

Case : {0 var : VarTy tyvar} -> {ds : _} -> (scrutinee : Expr tyvar var (Sum ds)) -> HList (CaseArms ds var motive) -> Expr tyvar var motive
Case {ds = []} e [] = Absurd e
Case {ds = (_ :: _)} e (arm :: arms) = Match e arm (\right => Case (Var right) arms)

0 lift : Ty tyvar u -> VarTy tyvar -> Type
lift a var = Expr tyvar var a

record Gen (0 u : U) (0 var : VarTy tyvar) (a : Type) where
  constructor MkGen
  unGen : {r : Ty tyvar u} -> (a -> lift r var) -> lift r var

runGen : {a : Ty tyvar u} -> Gen u var (lift a var) -> lift a var
runGen gen = unGen gen id

gen : {a : _} -> Expr tyvar var a -> Gen u var (Expr tyvar var a)
gen e = MkGen $ \k => Let _ e (\x => k (Var x))

interface Monad m => MonadGen (0 u : U) (0 var : VarTy tyvar) m | m where
  liftGen : Gen u var a -> m a

Functor (Gen u var) where
  map f fa = MkGen $ \k => unGen fa $ \fa => k (f fa)

Applicative (Gen u var) where
  pure a = MkGen $ \k => k a
  fa <*> a = MkGen $ \k => unGen fa $ \fa => unGen a $ \a => k (fa a)

covering
Monad (Gen u var) where
  m >>= f = MkGen $ \k => unGen m (\a => unGen (f a) k)

MonadGen u var (Gen u var) where
  liftGen gen = gen

-- https://github.com/AndrasKovacs/staged/blob/main/icfp24paper/supplement/haskell-cftt/CFTT/Improve.hs#L17
interface MonadGen Val var m => Improve (0 tyvar : Type) (0 var : VarTy tyvar) (0 f : ValTy tyvar -> Ty tyvar u) (0 m : Type -> Type) | m where
  up : {a : ValTy tyvar} -> lift (f a) var -> m (lift a var)
  down : {a : ValTy tyvar} -> m (lift a var) -> lift (f a) var

interface Split (0 tyvar : Type) (0 a : ValTy tyvar) | a where
  0 SplitTo : VarTy tyvar -> Type
  split : {0 var : VarTy tyvar} -> lift a var -> Gen Val var (SplitTo var)

data IdentityTag : Type where

Identity : ValTy tyvar -> ValTy tyvar
Identity a = Newtype IdentityTag a

Improve tyvar var Identity (Gen Val var) where
  up x = pure (Unwrap x)
  down x = unGen x (Wrap _)

List : ValTy tyvar -> ValTy tyvar
List a = Fix (\list => Sum [One, Product [a, TyVar list]])

{a : ValTy tyvar} -> Split tyvar (List a) where
  SplitTo var = Maybe (lift a var, lift (List a) var)
  split as = MkGen $ \k => Case (Unroll as %search) [\_ => k Nothing, \cons => k (Just (First (Var cons), First (Rest (Var cons))))]

-- Copied from https://github.com/idris-lang/Idris2/blob/ec74792a49bf4d22509172d1f03d153ffca1b95c/libs/papers/Search/Tychonoff/PartI.idr#L48
export infix 0 <->
record (<->) (a, b : Type) where
  constructor MkIso
  forwards  : a -> b
  backwards : b -> a
  inverseL  : (x : a) -> backwards (forwards x) === x
  inverseR  : (y : b) -> forwards (backwards y) === y

-- Not having eta for records is getting in the way of me proving things about
-- SOP from the sop package. So here's my own version...ish
0 SOP : (a -> Type) -> List (List a) -> Type
SOP f xs = NS_ (List a) (NP_ a f) xs

Uninhabited (SOP f []) where
  uninhabited sum impossible

namespace TreeExample
  TreeF : ValTy tyvar -> tyvar -> ValTy tyvar
  TreeF a = (\tree => Sum [One, Product [a, TyVar tree, TyVar tree]])

  Tree : ValTy tyvar -> ValTy tyvar
  Tree a = Fix $ TreeF a

  leaf : Expr tyvar var (Tree a)
  leaf = Roll (Left TT) %search

  node : Expr tyvar var a -> (l, r : Expr tyvar var (Tree a)) -> Expr tyvar var (Tree a)
  node n l r =
    Roll (Right $ Left $ Prod n (Prod l $ Prod r TT)) %search

  data TreeSplit : (0 var : VarTy tyvar) -> ValTy tyvar -> Type where
    Leaf : TreeSplit var a
    Node : Expr tyvar var a -> (l, r : Expr tyvar var (Tree a)) -> TreeSplit var a

  {a : _} -> Split tyvar (Tree {tyvar} a) where
    SplitTo var = TreeSplit var a
    split as = MkGen $ \k => Case (Unroll as %search) [\_ => k Leaf, \node => k (Node (First (Var node)) (First (Rest (Var node))) (First (Rest (Rest (Var node)))))]

  Nat : ValTy tyVar
  Nat = Fix (\nat => Sum [One, TyVar nat])

  data StateTTag : Type where

  StateT : ValTy var -> (ValTy var -> ValTy var) -> ValTy var -> CompTy var
  StateT s m a = Newtype StateTTag $ Fun s (m (Product [a, s]))

  Maybe : ValTy tyvar -> ValTy tyvar
  Maybe a = Sum [One, a]

  nothing : Expr tyvar var (Maybe a)
  nothing = Left TT

  just : Expr tyvar var a -> Expr tyvar var (Maybe a)
  just a = Right $ Left a

  {a : _} -> Split tyvar (Maybe a) where
    SplitTo var = Maybe (Expr tyvar var a)
    split ma = MkGen $ \k => Case ma [\_ => k Nothing, \a => k (Just (Var a))]

  data MaybeTTag : Type where

  public export
  MaybeT : (ValTy var -> Ty var u) -> ValTy var -> Ty var u
  MaybeT m a = Newtype MaybeTTag $ m (Maybe a)

  runMaybeT : Expr tyvar var (MaybeT m a) -> Expr tyvar var (m (Maybe a))
  runMaybeT = Unwrap

  MkMaybeT : Expr tyvar var (m (Maybe a)) -> Expr tyvar var (MaybeT m a)
  MkMaybeT = Wrap _

  MonadGen u var m => MonadGen u var (MaybeT m) where
    liftGen = lift . liftGen

  -- NOTE: For some reason, auto search can't find this, and it's rather
  -- annoying.
  [improveMaybeInstance]
  Improve tyvar var f m => Improve tyvar var (MaybeT f) (MaybeT m) where
    up x = MkMaybeT $ do
      ma <- up $ runMaybeT {m = f} x
      liftGen $ split ma
    down (MkMaybeT x) = MkMaybeT {m = f} $ down $ x >>= \case
      Nothing => pure nothing
      Just a => pure (just a)

  fail : Improve tyvar var f m => {a : _} -> Expr tyvar var (MaybeT f a)
  fail = down @{improveMaybeInstance} {f = MaybeT f, m = MaybeT m} nothing

  MonadGen u var m => MonadGen u var (StateT s m) where
    liftGen = lift . liftGen

  {s : _} -> Improve tyvar var f m => Improve tyvar var (StateT s f) (StateT (lift s var) m) where
    up x = ST $ \s => do
      h <- up {m = m} (App (Unwrap x) s)
      pure (First (Rest h), First h)
    down x = Wrap _ $ Lam _ $ \s => down {m = m} $ do
      (s, a) <- runStateT (Var s) x
      pure (Prod a (Prod s TT))

  Bool : ValTy var
  Bool = Sum [One, One]

  true : Expr tyvar var Bool
  true = Left TT

  false : Expr tyvar var Bool
  false = Right $ Left TT

  Split tyvar Bool where
    SplitTo var = Bool
    split b = MkGen $ \k => Case b [\_ => k True, \_ => k False]

  Split tyvar Nat where
    SplitTo var = Maybe (Expr tyvar var Nat)
    split n = MkGen $ \k => Case (Unroll n %search) [\_ => k Nothing, \n' => k (Just (Var n'))]

  (==) : Expr tyvar var (Fun Nat (Fun Nat Bool))
  (==) = flip (LetRec _) Var $ \eq =>
    Lam _ $ \n => Lam _ $ \m =>
      unGen (do
        case (!(split (Var n)), !(split (Var m))) of
          (Nothing, Nothing) => pure true
          (Just n', Just m') => pure $ App (App (Var eq) n') m'
          _ => pure false) id

  0 U_SOP : Type -> Type
  U_SOP tyvar = List (List (ValTy tyvar))

  0 El_SOP : U_SOP tyvar -> VarTy tyvar -> Type
  El_SOP a var = SOP (flip lift var) a

  interface IsSOP (0 a : Type) where
    Rep : U_SOP tyvar
    rep : {0 tyvar : Type} -> {0 var : VarTy tyvar} -> a <-> El_SOP (Rep {tyvar}) var

  0 sopEta : (x : SOP_ k f xs) -> MkSOP (unSOP x) === x
  sopEta (MkSOP sop) = Refl

  IsSOP a => IsSOP (Maybe a) where
    Rep = [] :: Rep {a}
    rep = MkIso {
      forwards = \case
        Nothing => Z []
        Just x => S (rep.forwards x),
      backwards = \case
        Z [] => Nothing
        S sop => Just (rep.backwards sop),
      inverseL = \case
        Nothing => Refl
        Just x =>
          cong Just $
          --let etaPrf = sopEta (rep.forwards x) in
          --replace {p = \sop => rep.backwards sop === x, x = rep.forwards x, y = rep.forwards x} (sym etaPrf)
          (rep.inverseL x),
      inverseR = \case
        Z [] => Refl
        S sop =>
          cong S $ rep.inverseR sop
    }

  distributeSop : List a -> List (List a) -> List (List a)
  distributeSop pa [] = []
  distributeSop pa (pb :: pbs) = (pa ++ pb) :: distributeSop pa pbs

  cartesianSop : (sopa, sopb : List (List a)) -> List (List a)
  cartesianSop [] _ = []
  cartesianSop (pa :: pas) sopb = distributeSop pa sopb ++ cartesianSop pas sopb

  leftSop : SOP f kss -> SOP f (kss ++ lss)
  leftSop (Z a) = Z a
  leftSop (S a) = S (leftSop a)

  rightSop : {lss : List (List a)} -> SOP f kss -> SOP f (lss ++ kss)
  rightSop {lss = []} x = x
  rightSop {lss = ls :: lss} x = S (rightSop x)

  pairPSop : NP f ks -> SOP f kss -> SOP f (distributeSop ks kss)
  pairPSop x (Z y) = Z (append x y)
  pairPSop x (S y) = S (pairPSop x y)

  sopProduct : {kss, lss : List (List k)} -> SOP f kss -> SOP f lss -> SOP f (cartesianSop kss lss)
  sopProduct {kss = .(ks :: kss)} (Z v) y = leftSop (pairPSop v y)
  sopProduct (S x) y = rightSop (sopProduct x y)

  splitNs : (ks : List k) -> NS f (ks ++ ls) -> Either (NS f ks) (NS f ls)
  splitNs [] s = Right s
  splitNs (x :: xs) (Z v) = Left (Z v)
  splitNs (x :: xs) (S y) = mapFst S (splitNs xs y)

  -- Using this instead of `Data.SOP.NP.narrow` to make proofs easier.
  unpairP : {a : List k} -> NP f (a ++ b) -> (NP f a, NP f b)
  unpairP {a = []} x = ([], x)
  unpairP {a = (a :: as)} (x :: y) =
    mapFst (x ::) $ unpairP {a = as} y

  unpairPNs : (ks : List k) -> (lss : List (List k)) -> NS (NP f) (distributeSop ks lss) -> (NP f ks, NS (NP f) lss)
  unpairPNs _ [] s impossible
  unpairPNs ks (x :: xs) (Z p) = mapSnd Z (unpairP p)
  unpairPNs ks (x :: xs) (S s) = mapSnd S (unpairPNs _ _ s)

  unpairSop : (kss, lss : List (List k)) -> SOP f (cartesianSop kss lss) -> (SOP f kss, SOP f lss)
  unpairSop (ks :: kss) (ls :: lss) (Z v) =
    bimap Z Z (unpairP v)
  unpairSop (ks :: kss) (ls :: lss) (S x) =
    case splitNs (distributeSop ks lss) x of
      Left x =>
        let unpaired = unpairPNs _ _ x in (Z (fst unpaired), (S (snd unpaired)))
      Right x => mapFst S (unpairSop _ _ x)
  unpairSop [] _ sop impossible
  unpairSop (ks :: kss) [] sop = absurd (snd (unpairSop kss [] sop))

  0 pairPBeta : (v : NP f ks) -> {x : NP f ls} -> unpairP (append v x) = (v, x)
  pairPBeta [] = Refl
  pairPBeta (v :: vs) = cong (mapFst (v ::)) (pairPBeta vs)

  0 pAppendHetCong : {0 vs : NP f ks} -> {0 ws : NP f ls} -> (0 x : f a) -> vs ~=~ ws -> (x :: vs) ~=~ (x :: ws)
  pAppendHetCong x Refl = Refl

  %unbound_implicits off
  hetCong : {0 d : Type} -> (0 p, c : d -> Type) -> {0 a, b : d} -> {0 x : p a} -> {0 y : p b} -> (0 f : forall a. p a -> c a) -> a = b -> x ~=~ y -> f x ~=~ f y
  hetCong p c f Refl Refl = Refl

  hetTrans : {0 a, b, c : Type} -> (0 x : a) -> (0 y : b) -> (0 z : c) -> x ~=~ y -> y ~=~ z -> x ~=~ z
  hetTrans x x x Refl Refl = Refl
  %unbound_implicits on

  0 pAppendRightId : (vs : NP f ks) -> append vs [] ~=~ vs
  pAppendRightId [] = Refl
  pAppendRightId {ks = .(k :: ks)} (v :: vs) = hetCong (NP f) (NP f . (k ::)) (v ::) (appendNilRightNeutral ks) (pAppendRightId vs)

  0 etaPair : (x : (a, b)) -> (fst x, snd x) = x
  etaPair (x1, x2) = Refl

  0 pairPEta : (ks, ls : List k) -> (p : NP f (ks ++ ls)) -> append {ks, ks' = ls} (fst (unpairP {a = ks, b = ls} p)) (snd (unpairP {a = ks, b = ls} p)) = p
  pairPEta [] ls p = Refl
  pairPEta (k :: ks) ls (v :: vs) =
    replace {p = \up => append (fst (bimap (\arg => v :: arg) id up)) (snd (bimap (\arg => v :: arg) id up)) = v :: vs} (etaPair (unpairP vs)) $
    cong (v ::) $ pairPEta ks ls vs

  0 leftSopBeta : {0 lss : List (List k)} -> (s : NS (NP f) kss) -> splitNs kss {ls = lss} (leftSop {lss} s) = Left s
  leftSopBeta (Z v) = Refl
  leftSopBeta {kss = .(_ :: kss)} (S x) =
    rewrite leftSopBeta {k, lss, f, kss} x in
    Refl

  0 rightSopBeta : (kss : List (List k)) -> splitNs kss (rightSop {lss = kss} sop) = Right sop
  rightSopBeta [] = Refl
  rightSopBeta (x :: xs) =
    rewrite rightSopBeta xs {sop} in
    Refl

  0 pairPSopBeta : (x : NS (NP f) lss) -> unpairPNs ks lss (pairPSop v x) = (v, x)
  pairPSopBeta (Z x) =
    trans (cong (mapSnd Z) (pairPBeta v)) Refl
  pairPSopBeta (S x) = rewrite pairPSopBeta x {v} in Refl

  0 pairSopBeta : (sopA : SOP f kss) -> (sopB : SOP f lss) -> unpairSop kss lss (sopProduct sopA sopB) = (sopA, sopB)
  pairSopBeta {kss = .(ks :: kss), lss = .(ls :: lss)} (Z v) (Z x) =
    trans (cong (bimap Z Z) (pairPBeta v)) Refl
  pairSopBeta {kss = .(ks :: kss), lss = .(ls :: lss)} (Z v) (S x) =
    let lsb = leftSopBeta {lss = cartesianSop kss (ls :: lss), f, kss = distributeSop ks lss} (pairPSop v x) in
    rewrite lsb in
    cong2 (,) (cong (Z . fst) $ pairPSopBeta x) (cong (S . snd) $ pairPSopBeta x)
  pairSopBeta {kss = .(ks :: ks2 :: kss), lss = .(ls :: lss)} (S x) sopB@(Z v) =
    rewrite rightSopBeta (distributeSop ks lss) {sop = sopProduct x sopB} in
    rewrite pairSopBeta {kss = (ks2 :: kss), lss = (ls :: lss)} x sopB in
    Refl
  pairSopBeta {kss = .(ks :: ks2 :: kss), lss = .(ls :: ls2 :: lss)} (S x) sopB@(S y) =
    rewrite rightSopBeta (distributeSop ks lss) {sop = sopProduct x sopB} in
    rewrite pairSopBeta {kss = (ks2 :: kss), lss = (ls :: ls2 :: lss)} x sopB in
    Refl
  pairSopBeta {kss = .(ks :: ks2 :: kss), lss = .([_])} (S x) (S y) impossible
  pairSopBeta {kss = .(ks :: [])} (S x) y impossible
  pairSopBeta {kss = []} x s impossible
  pairSopBeta {lss = []} x s impossible

  0 pairPSopEta : (ys : List (List k)) -> (distSop : SOP f (distributeSop y ys)) -> pairPSop (fst (unpairPNs y ys distSop)) (snd (unpairPNs y ys distSop)) = distSop
  pairPSopEta [] distSop impossible
  pairPSopEta (x :: xs) (Z p) =
    rewrite sym $ etaPair {a = NP f y, b = NP f x} (unpairP p) in
    cong Z $
    pairPEta _ _ p
  pairPSopEta (x :: xs) (S s) =
    rewrite sym $ etaPair (unpairPNs y xs s) in
    cong S $
    pairPSopEta xs s

  bimapLeftInvert : (x : Either _ _) -> {0 y : _} -> bimap f g x = Left y -> (z : _ ** x = Left z)
  bimapLeftInvert (Left x) prf = (x ** Refl)
  bimapLeftInvert (Right _) Refl impossible

  bimapRightInvert : (x : Either _ _) -> {0 y : _} -> bimap f g x = Right y -> (z : _ ** x = Right z)
  bimapRightInvert (Right _) prf = (_ ** Refl)

  Injective (NS.S {f, ks, t}) where
    injective Refl = Refl

  splitLeftInvert :
    (xs : List (List k)) ->
    (ys : List (List k)) ->
    (s : NS_ (List k) (NP_ k f) (ys ++ xs)) ->
    {distSop : SOP f ys} ->
    splitNs ys {ls = xs} s = Left distSop ->
    leftSop {lss = xs, kss = ys} distSop = s
  splitLeftInvert xs [] s prf impossible
  splitLeftInvert xs (x :: ys) (Z s) {distSop = Z s} Refl = Refl
  splitLeftInvert xs (x :: ys) (S s) {distSop = Z p} prf with (splitNs ys s)
    _ | Left _ impossible
    _ | Right _ impossible
  splitLeftInvert xs (x :: ys) (Z s) {distSop = S distSop} prf impossible
  splitLeftInvert xs (x :: ys) (S s) {distSop = S distSop} prf =
    let (z ** invertPrf) = bimapLeftInvert (splitNs ys s) prf
        helperPrf = inj @{ComposeInjective {f = NS.S, g = Left}} (Left . S) $ trans (sym prf) $ cong (bimap S id) invertPrf in
    cong S $
    splitLeftInvert xs _ {k, f, distSop} s $
    trans invertPrf $
    cong Left (sym helperPrf)

  splitRightInvert :
    (xs : List (List k)) ->
    (ys : List (List k)) ->
    (s : NS_ (List k) (NP_ k f) (ys ++ xs)) ->
    {sop : SOP f xs} ->
    splitNs ys {ls = xs} s = Right sop ->
    rightSop {lss = ys, kss = xs} sop = s
  splitRightInvert [] _ _ _ impossible
  splitRightInvert (x :: xs) [] s Refl = Refl
  splitRightInvert (x :: xs) (y :: ys) (Z v) prf impossible
  splitRightInvert (x :: xs) (y :: ys) (S z) prf =
    let (w ** invertPrf) = bimapRightInvert (splitNs ys z) prf
        helperPrf = inj Right $ trans (sym prf) $ cong (bimap S id) invertPrf in
    cong S $
    splitRightInvert (x :: xs) _ z $
    trans invertPrf $
    sym $ cong Right helperPrf

  0 pairSopEta : (kss, lss : List (List k)) -> (x : SOP f (cartesianSop kss lss)) -> sopProduct (fst (unpairSop kss lss x)) (snd (unpairSop kss lss x)) = x
  pairSopEta [] _ x impossible
  pairSopEta (y :: xs) [] x = absurd (snd (unpairSop xs [] x))
  pairSopEta (y :: xs) (z :: ys) (Z p) =
    rewrite sym $ etaPair {a = NP f y, b = NP f z} (unpairP p) in
    cong Z $ pairPEta _ _ p
  pairSopEta (y :: xs) (z :: ys) (S s) with (splitNs (distributeSop y ys) s) proof prf
    _ | Left distSop =
      cong S $
      rewrite pairPSopEta {y} ys distSop in
      splitLeftInvert _ _ _ prf
    _ | Right cartSop =
      rewrite sym $ etaPair (unpairSop xs (z :: ys) cartSop) in
      trans (cong (S . rightSop) (pairSopEta _ _ cartSop)) $
      cong S $ splitRightInvert _ _ _ prf

  -- https://github.com/AndrasKovacs/staged/blob/fe63229afeaec8caad3f46e1a33337fdab712982/icfp24paper/supplement/agda-cftt/SOP.agda#L286
  IsSOP a => IsSOP b => IsSOP (a, b) where
    Rep = cartesianSop (Rep {a}) (Rep {a = b})
    rep = MkIso {
      forwards = \x =>
        sopProduct (rep.forwards (fst x)) (rep.forwards (snd x)),
      backwards = \x =>
        let pair = unpairSop (Rep {a}) (Rep {a = b}) x in
        (rep.backwards (fst pair), rep.backwards (snd pair)),
      inverseL = \x =>
        let psb = irrelevantEq $ pairSopBeta {kss = Rep {a}, lss = Rep {a = b}} (rep.forwards (fst x)) (rep.forwards (snd x)) in
        replace {p = \pair => (rep.backwards (Builtin.fst pair), rep.backwards (Builtin.snd pair)) === x, x = (rep.forwards (fst x), rep.forwards (snd x))} (sym psb) $
        case x of
          (first, second) => cong2 (,) (rep.inverseL first) (rep.inverseL second),
      inverseR = \x =>
        let fstInverseR = rep.inverseR (fst (unpairSop (Rep {a}) (Rep {a = b}) x))
            sndInverseR = rep.inverseR (snd (unpairSop (Rep {a}) (Rep {a = b}) x))
            recInverseR = cong2 sopProduct fstInverseR sndInverseR in
        trans recInverseR $ pairSopEta _ _ x
    }

    {-
  0 Fun_SOPLift : U_SOP tyvar -> Ty tyvar u -> VarTy tyvar -> Type
  Fun_SOPLift [] r _ = ()
  Fun_SOPLift (a :: b) r var = (lift (snd $ foldr (\d, uc => (Comp ** Fun d $ snd uc)) (the (u : U ** Ty tyvar u) (u ** r)) a) var, Fun_SOPLift b r var)

  covering
  tabulate : {a : _} -> (El_SOP a var -> lift r var) -> Fun_SOPLift a r var
  tabulate {a = []} f = ()
  tabulate {a = ([] :: xs)} f = (f $ MkSOP $ Z [], tabulate {a = xs} $ \(MkSOP sop) => f (MkSOP $ S sop))
  tabulate {a = ((x :: ys) :: xs)} f =
    let rec = TreeExample.tabulate $ \(MkSOP sop) => f (MkSOP $ S sop)
        rec2 = \x => tabulate {a = (ys :: xs)} $ \(MkSOP sop) => f $ MkSOP $ case sop of
          Z p => Z (x :: p)
          S p => S p in
    (Lam _ $ \arg => (fst $ rec2 (Var arg)), rec)

  covering
  index : {a : _} -> Fun_SOPLift a r var -> (El_SOP a var -> lift r var)
  index {a = []} fs = absurd
  index {a = ([] :: xs)} (res, fs) = \case
    MkSOP (Z _) => res
    MkSOP (S p) => index fs (MkSOP p)
  index {a = ((x :: ys) :: xs)} (f, fs) = \case
    MkSOP (Z (first :: rest)) =>
      let app = App f first
          rec = index {a = (ys :: xs)} (app, fs) in
      rec (MkSOP (Z rest))
    MkSOP (S p) => index fs (MkSOP p)

  %unbound_implicits off
  genFun_SOPLift : {0 tyvar : Type} -> {a : U_SOP tyvar} -> {v : U} -> {r : Ty tyvar v} -> {0 u : U} -> {0 var : VarTy tyvar} -> Fun_SOPLift a r var -> Gen u var (Fun_SOPLift a r var)
  genFun_SOPLift {a = []} () = pure ()
  genFun_SOPLift {a = (_ :: a)} (f, fs) = [| (gen f, genFun_SOPLift fs) |]
  %unbound_implicits on

  interface Monad m => MonadJoin m where
    join : IsSOP a => m a -> m a

  covering
  {u : U} -> MonadJoin (Gen u var) where
    join ma = MkGen $ \k => runGen $ do
      joinPoints <- genFun_SOPLift (tabulate (k . rep.backwards))
      a <- ma
      pure $ index joinPoints (rep.forwards a)

  MonadJoin m => MonadJoin (MaybeT m) where
    join (MkMaybeT ma) = MkMaybeT (join ma)

  MonadJoin m => MonadJoin (ReaderT r m) where
    join (MkReaderT ma) = MkReaderT (join . ma)

  MonadJoin m => IsSOP s => MonadJoin (StateT s m) where
    join (ST ma) = ST (join . ma)

    {-
  f : Expr tyvar var (Fun (Tree Nat) (StateT (List Nat) (MaybeT Identity) (Tree Nat)))
  f = LetRec _ (\f =>
    Lam (Tree Nat) $ \t => down $ do
      treeSplit <- liftGen $ split (the (Expr tyvar var (Tree Nat)) $ Var t)
      case treeSplit of
        Leaf => pure leaf
        Node n l r => do
          case !(liftGen $ split (App (App (==) n) 0)) of
            True => fail
            False => pure ()
          ns <- get
          n <- join $ case !(liftGen $ split $ the (Expr tyvar var (List Nat)) ns) of
            Nothing => pure n
            Just (n, ns) => do
              put ns
              pure n
          l <- up (App (Var f) l)
          r <- up (App (Var f) r)
          pure (node n l r)) Var
