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
import Data.Morphisms.Iso
import Data.SOP
import Data.Vect
import Data.Vect.Quantifiers
import Syntax.WithProof
import TwoLTT.Expr
import TwoLTT.Types

%default total

%hide Data.SOP.SOP.SOP

0 CaseArms : {n : Nat} -> (0 ds : Vect n (Ty tyvar Val)) -> VarTy tyvar -> Ty tyvar u -> Vect n Type
CaseArms {n = 0} _ var mot = []
CaseArms {n = S n} ds var mot =
  (var _ (head ds) -> Expr var mot) :: CaseArms (tail ds) var mot

Case : {0 var : VarTy tv} -> {0 n : Nat} -> {0 ds : Vect n (Ty tv Val)} -> {0 motive : Ty tv u} -> (scrutinee : Expr var (Sum ds)) -> HVect (CaseArms ds var motive) -> Expr var motive
Case e [] {ds} =
  Absurd $ rewrite (sym $ invertVectZ ds) in e
Case e (arm :: arms) = Match e arm (\right => Case (Var right) arms)

record Gen (0 u : U) (0 var : VarTy tv) (a : Type) where
  constructor MkGen
  -- `r` is explicit because of https://github.com/idris-lang/Idris2/issues/3533.
  unGen : (0 r : Ty tv u) -> (a -> Expr var r) -> Expr var r

runGen : {0 a : Ty tv u} -> Gen u var (Expr var a) -> Expr var a
runGen gen = unGen gen _ id

gen : {v : U} -> {0 a : Ty tv v} -> Expr var a -> Gen u var (Expr var a)
gen e = MkGen $ \_, k => Let _ e (\x => k (Var x))

interface Monad m => MonadGen (0 u : U) (0 var : VarTy tv) m | m where
  liftGen : Gen u var a -> m a

Functor (Gen u var) where
  map f fa = MkGen $ \_, k => unGen fa _ $ \fa => k (f fa)

Applicative (Gen u var) where
  pure a = MkGen $ \_, k => k a
  fa <*> a = MkGen $ \_, k => unGen fa _ $ \fa => unGen a _ $ \a => k (fa a)

covering
Monad (Gen u var) where
  m >>= f = MkGen $ \_, k => unGen m _ (\a => unGen (f a) _ k)

MonadGen u var (Gen u var) where
  liftGen gen = gen

-- https://github.com/AndrasKovacs/staged/blob/main/icfp24paper/supplement/haskell-cftt/CFTT/Improve.hs#L17
interface MonadGen Val var m => Improve (0 var : VarTy tyvar) (0 f : Ty tyvar Val -> Ty tyvar u) (0 m : Type -> Type) | m where
  up : {0 a : Ty _ Val} -> Expr var (f a) -> m (Expr var a)
  down : (0 a : Ty _ Val) -> m (Expr var a) -> Expr var (f a)

interface Split (0 a : Ty tyvar Val) where
  0 SplitTo : VarTy tyvar -> Type
  split : (0 var : VarTy _) -> Expr var a -> Gen Val var (SplitTo var)

data IdentityTag : Type where

Identity : Ty tyvar Val -> Ty tyvar Val
Identity a = Newtype IdentityTag a

Improve var Identity (Gen Val var) where
  up x = pure (Unwrap x)
  down _ x = unGen x _ (Wrap _)

List : Ty tyvar Val -> Ty tyvar Val
List a = Fix (\list => Sum [One, Product [a, TyVar list]])

{0 a : Ty tyvar Val} -> Split (List a) where
  SplitTo var = Maybe (Expr var a, Expr var (List a))
  split _ as = MkGen $ \_, k =>
    Case (Unroll as %search) [
      \_ => k Nothing,
      \cons => k (Just (First (Var {ty = Product [a, List a]} cons), First (Rest (Var {ty = Product [a, List a]} cons))))
    ]

-- Not having eta for records is getting in the way of me proving things about
-- SOP from the sop package. So here's my own version...ish
0 SOP : (a -> Type) -> List (List a) -> Type
SOP f xs = NS_ (List a) (NP_ a f) xs

Uninhabited (SOP f []) where
  uninhabited sum impossible

namespace TreeExample
  TreeF : Ty tyvar Val -> tyvar -> Ty tyvar Val
  TreeF a = (\tree => Sum [One, Product [a, TyVar tree, TyVar tree]])

  Tree : Ty tyvar Val -> Ty tyvar Val
  Tree a = Fix $ TreeF a

  leaf : {0 a : Ty tyvar Val} -> Expr var (Tree a)
  leaf = Roll (Left TT) %search

  node : {0 a : Ty tyvar Val} -> Expr var a -> (l, r : Expr var (Tree a)) -> Expr var (Tree a)
  node n l r =
    Roll (Right $ Left $ Prod n (Prod l $ Prod r TT)) %search

  data TreeSplit : (0 var : VarTy tyvar) -> Ty tyvar Val -> Type where
    Leaf : {0 a : Ty tyvar Val} -> TreeSplit var a
    Node : {0 a : Ty tyvar Val} -> Expr var a -> (l, r : Expr var (Tree a)) -> TreeSplit var a

  {0 a : Ty tyvar Val} -> Split (Tree a) where
    SplitTo var = TreeSplit var a
    split _ as = MkGen $ \_, k =>
      Case (Unroll as %search) [\_ => k Leaf, \node => k (Node (First (Var node)) (First (Rest (Var node))) (First (Rest (Rest (Var node)))))]

  Nat : Ty tyVar Val
  Nat = Fix (\nat => Sum [One, TyVar nat])

  data StateTTag : Type where

  StateT : Ty var Val -> (Ty var Val -> Ty var Val) -> Ty var Val -> Ty var Comp
  StateT s m a = Newtype StateTTag $ Fun s (m (Product [a, s]))

  Maybe : Ty tyvar Val -> Ty tyvar Val
  Maybe a = Sum [One, a]

  nothing : {0 a : Ty tyvar Val} -> Expr var (Maybe a)
  nothing = Left TT

  just : {0 a : Ty tyvar Val} -> Expr var a -> Expr var (Maybe a)
  just a = Right $ Left a

  {0 a : Ty tyvar Val} -> Split (Maybe a) where
    SplitTo var = Maybe (Expr var a)
    split _ ma = MkGen $ \_, k => Case ma [\_ => k Nothing, \a => k (Just (Var a))]

  data MaybeTTag : Type where

  public export
  MaybeT : (Ty var Val -> Ty var u) -> Ty var Val -> Ty var u
  MaybeT m a = Newtype MaybeTTag $ m (Maybe a)

  runMaybeT : {0 m : Ty tv Val -> Ty tv u} -> {0 a : Ty tv Val} -> Expr var (MaybeT m a) -> Expr var (m (Maybe a))
  runMaybeT = Unwrap

  MkMaybeT : {0 m : Ty tv Val -> Ty tv u} -> {0 a : Ty tv Val} -> Expr var (m (Maybe a)) -> Expr var (MaybeT m a)
  MkMaybeT = Wrap _

  MonadGen u var m => MonadGen u var (MaybeT m) where
    liftGen = lift . liftGen

  -- NOTE: For some reason, auto search can't find this, and it's rather
  -- annoying.
  [improveMaybeInstance]
  {0 f : Ty tv Val -> Ty tv u} -> Improve var f m => Improve var (MaybeT f) (MaybeT m) where
    up x = MkMaybeT $ do
      ma <- up $ runMaybeT {m = f} x
      liftGen $ split _ ma
    down _ (MkMaybeT x) = MkMaybeT {m = f} $ down _ $ x >>= \case
      Nothing => pure nothing
      Just a => pure (just a)

  fail : {0 f : Ty tv Val -> Ty tv u} -> Improve var f m => {0 a : Ty tv Val} -> Expr var (MaybeT f a)
  fail = down _ @{improveMaybeInstance} {m = MaybeT m} nothing

  MonadGen u var m => MonadGen u var (StateT s m) where
    liftGen = lift . liftGen

  [improveStateInstance]
  {0 f : Ty tv Val -> Ty tv Val} -> {0 s : Ty tv Val} -> Improve var f m => Improve var (StateT s f) (StateT (Expr var s) m) where
    up x = ST $ \s => do
      h <- up {m = m} (App (Unwrap x) s)
      pure (First (Rest h), First h)
    down _ x = Wrap _ $ Lam _ $ \s => down _ {m = m} $ do
      (s, a) <- runStateT (Var s) x
      pure (Prod a (Prod s TT))

  data BoolTag : Type where

  Bool : Ty var Val
  Bool = Newtype BoolTag $ Sum [One, One]

  true : Expr var Bool
  true = Wrap _ $ Left TT

  false : Expr var Bool
  false = Wrap _ $ Right $ Left TT

  Split Bool where
    SplitTo var = Bool
    split _ b = MkGen $ \_, k => Case (Unwrap b) [\_ => k True, \_ => k False]

  Split Nat where
    SplitTo var = Maybe (Expr var Nat)
    split _ n = MkGen $ \_, k => Case (Unroll n %search) [\_ => k Nothing, \n' => k (Just (Var n'))]

  (==) : Expr var (Fun Nat (Fun Nat Bool))
  (==) = flip (LetRec _) Var $ \eq =>
    Lam _ $ \n => Lam _ $ \m =>
      unGen (do
        case (!(split _ (Var n)), !(split _ (Var m))) of
          (Nothing, Nothing) => pure true
          (Just n', Just m') => pure $ App (App (Var eq) n') m'
          _ => pure false) _ id

  0 U_SOP : Type -> Type
  U_SOP tv = List (List (Ty tv Val))

  0 El_SOP : U_SOP tv -> VarTy tv -> Type
  El_SOP a var = SOP (Expr var) a

  0 El_SOP' : U_SOP tv -> Type
  El_SOP' a = forall var. El_SOP a var

  interface IsSOP (0 tv : Type) (0 var : VarTy tv) (0 a : Type) | a where
    Rep : U_SOP tv
    rep : a <-> El_SOP Rep var

  {0 var : VarTy tv} -> IsSOP tv var a => IsSOP tv var (Maybe a) where
    Rep = [] :: Rep {var, a}
    rep = MkIso {
      forwards = \case
        Nothing => Z []
        Just x => S ((rep {var}).forwards x),
      backwards = \case
        Z [] => Nothing
        S sop => Just ((rep {var}).backwards sop),
      inverseL = \case
        Nothing => Refl
        Just x =>
          cong Just ((rep {var}).inverseL x),
      inverseR = \case
        Z [] => Refl
        S sop =>
          cong S $ (rep {var}).inverseR sop
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
  IsSOP tv var a => IsSOP tv var b => IsSOP tv var (a, b) where
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

  MultiArgFunU : List _ -> U -> U
  MultiArgFunU [] = id
  MultiArgFunU _ = const Comp

  MultiArgFun : (args : List (Ty tv Val)) -> Ty tv u -> Ty tv (MultiArgFunU args u)
  MultiArgFun [] ret = ret
  MultiArgFun (arg :: args) ret = Fun arg (MultiArgFun args ret)

  0 Fun_SOPLift : U_SOP tv -> Ty tv u -> VarTy tv -> Type
  Fun_SOPLift [] r _ = ()
  Fun_SOPLift (a :: b) r var = (Expr var (MultiArgFun a r), Fun_SOPLift b r var)

  tabulate : {a : _} -> {u : U} -> {0 r : Ty tv u} -> (El_SOP a var -> Expr var r) -> Fun_SOPLift a r var
  tabulate {a = []} f = ()
  tabulate {a = ([] :: xs)} f = (f $ Z [], tabulate {a = xs} $ \sop => f (S sop))
  tabulate {a = ((x :: ys) :: xs)} f =
    let rec = TreeExample.tabulate $ \sop => f (S sop)
        rec2 : Expr var x -> Fun_SOPLift (ys :: xs) r var = \x =>
          tabulate {a = (ys :: xs)} $ \sop => f $ case sop of
            Z p => Z (x :: p)
            S p => S p in
    (Lam _ (fst . rec2 . Var), rec)

  index : {a : _} -> {0 r : Ty tv u} -> Fun_SOPLift a r var -> (El_SOP a var -> Expr var r)
  index {a = []} fs s = absurd s
  index {a = ([] :: xs)} (res, fs) (Z _) = res
  index {a = ([] :: xs)} (res, fs) (S p) = index fs p
  index {a = ((x :: ys) :: xs)} (f, fs) (Z (first :: rest)) =
    let app = App f first
        rec = index {a = (ys :: xs)} (app, fs) in
    rec (Z rest)
  index {a = ((x :: ys) :: xs)} (f, fs) (S p) = index fs p

  %unbound_implicits off
  genFun_SOPLift :
    {0 tv : Type} ->
    {a : U_SOP tv} ->
    {v : U} ->
    {0 r : Ty tv v} ->
    {0 u : U} ->
    {0 var : VarTy tv} ->
    Fun_SOPLift a r var ->
    Gen u var (Fun_SOPLift a r var)
  genFun_SOPLift {a = []} () = pure ()
  genFun_SOPLift {a = (ps :: a)} (f, fs) = [| (,) (gen f) (genFun_SOPLift fs) |]
  %unbound_implicits on

  interface Monad m => MonadJoin (0 var : VarTy tv) m | m where
    join : IsSOP _ var a => m a -> m a

  {u : U} -> MonadJoin var (Gen u var) where
    join ma = MkGen $ \_, k => runGen $ do
      joinPoints <- genFun_SOPLift (tabulate (k . rep.backwards))
      a <- ma
      pure $ index joinPoints (rep.forwards a)

  MonadJoin var m => MonadJoin var (MaybeT m) where
    join (MkMaybeT ma) = MkMaybeT (join ma)

  MonadJoin var m => MonadJoin var (ReaderT r m) where
    join (MkReaderT ma) = MkReaderT (join . ma)

  MonadJoin var m => IsSOP tv var s => MonadJoin var (StateT s m) where
    join (ST ma) = ST (join . ma)

  fromInteger : (n : Integer) -> Expr v Nat
  fromInteger n = if n <= 0 then Roll (Left TT) %search else Roll (Right $ Left $ assert_total $ TreeExample.fromInteger (n - 1)) %search

  -- TODO: Erase a
  {a : Ty tv Val} -> IsSOP tv v (Expr v a) where
    Rep = [[a]]
    rep = MkIso {
      forwards = \e => Z [e],
      backwards = \(Z [e]) => e,
      inverseL = \e => Refl,
      inverseR = \(Z [e]) => Refl
    }

  f : Expr var (Fun (Tree Nat) (StateT (List Nat) (MaybeT Identity) (Tree Nat)))
  f =
    LetRec _ (\f =>
      Lam (Tree Nat) $ \t => down @{improveStateInstance @{improveMaybeInstance}} _ $ do
        treeSplit <- liftGen {m = StateT (Expr var (List Nat)) (MaybeT (Gen Val var)), var} $ split var (the (Expr var (Tree Nat)) $ Var t)
        case treeSplit of
          Leaf => pure leaf
          Node n l r => do
            b <- liftGen $ split _ (App (App (==) n) 0)
            case b of
              True => lift nothing
              False => pure ()
            ns <- State.get
            n <- TreeExample.join {var} $ case !(liftGen {var} $ split var $ the (Expr var (List Nat)) ns) of
              Nothing => pure n
              Just (n, ns) => do
                put ns
                pure n
            l <- up @{improveStateInstance @{improveMaybeInstance}} (App (Var f) l)
            r <- up @{improveStateInstance @{improveMaybeInstance}} (App (Var f) r)
            pure (node n l r)) Var
