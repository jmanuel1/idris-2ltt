module TwoLTT.JoinPoints

import Control.Monad.Maybe
import Control.Monad.Reader
import Control.Monad.State
import Data.Either
import Data.Morphisms.Iso
import Data.SOP.NS
import TwoLTT.Expr
import TwoLTT.Gen
import TwoLTT.Types

%default total

public export
data NP_ : (0 a : Type) -> (a -> Type) -> List a -> Type where
  Nil : NP_ a f []
  (::) : f x -> NP_ a f xs -> NP_ a f (x :: xs)

public export
0 NP : (a -> Type) -> List a -> Type
NP f xs = NP_ a f xs

append : NP f ks -> NP f ks' -> NP f (ks ++ ks')
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

-- Not having eta for records is getting in the way of me proving things about
-- SOP from the sop package. So here's my own version
public export
0 SOP : (a -> Type) -> List (List a) -> Type
SOP f xs = NS_ (List a) (\xs => NP_ a f xs) xs

export
Uninhabited (SOP f []) where
  uninhabited sum impossible

public export
0 U_SOP : Type -> Type
U_SOP tv = List (List (Ty tv Val))

public export
0 El_SOP : U_SOP tv -> VarTy tv -> Type
El_SOP a var = SOP (Expr var) a

public export
0 El_SOP' : U_SOP tv -> Type
El_SOP' a = forall var. El_SOP a var

public export
interface IsSOP (0 tv : Type) (0 var : VarTy tv) (0 a : Type) | a where
  Rep : U_SOP tv
  rep : a <-> El_SOP Rep var

export
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
unpairP {a = a :: as} (x :: y) =
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

%unbound_implicits off
hetCong : {0 d : Type} -> (0 p, c : d -> Type) -> {0 a, b : d} -> {0 x : p a} -> {0 y : p b} -> (0 f : forall a. p a -> c a) -> a = b -> x ~=~ y -> f x ~=~ f y
hetCong p c f Refl Refl = Refl

hetTrans : {0 a, b, c : Type} -> (0 x : a) -> (0 y : b) -> (0 z : c) -> x ~=~ y -> y ~=~ z -> x ~=~ z
hetTrans x x x Refl Refl = Refl
%unbound_implicits on

0 etaPair : (x : (a, b)) -> (fst x, snd x) = x
etaPair (x1, x2) = Refl

0 pairPEta : (ks, ls : List k) -> (p : NP f (ks ++ ls)) -> append {ks, ks' = ls} (fst (unpairP {a = ks, b = ls} p)) (snd (unpairP {a = ks, b = ls} p)) = p
pairPEta [] ls p = Refl
pairPEta (k :: ks) ls (v :: vs) =
  replace {p = \up => append (fst (bimap (\arg => v :: arg) id up)) (snd (bimap (\arg => v :: arg) id up)) = v :: vs} (etaPair (unpairP vs)) $
  cong (v ::) $ pairPEta ks ls vs

0 leftSopBeta :
  {0 lss : List (List k)} ->
  {0 f : k -> Type} ->
  (s : NS (NP f) kss) ->
  splitNs kss {ls = lss} (leftSop {lss} s) = Left s
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
export
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

export
{a : Ty tv Val} -> IsSOP tv v (Expr v a) where
  Rep = [[a]]
  rep = MkIso {
    forwards = \e => Z [e],
    backwards = \(Z [e]) => e,
    inverseL = \e => Refl,
    inverseR = \(Z [e]) => Refl
  }

public export
interface Monad m => MonadJoin (0 var : VarTy tv) m | m where
  join : IsSOP _ var a => m a -> m a

export
MonadJoin var m => MonadJoin var (MaybeT m) where
  join (MkMaybeT ma) = MkMaybeT (join ma)

export
MonadJoin var m => MonadJoin var (ReaderT r m) where
  join (MkReaderT ma) = MkReaderT (join . ma)

export
MonadJoin var m => IsSOP tv var s => MonadJoin var (StateT s m) where
  join (ST ma) = ST (join . ma)

public export
MultiArgFunU : Nat -> U -> U
MultiArgFunU 0 = id
MultiArgFunU _ = const Comp

public export
MultiArgFun : (args : List (Ty tv Val)) -> {u : U} -> Ty tv u -> Ty tv (MultiArgFunU (length args) u)
MultiArgFun [] ret = ret
MultiArgFun (arg :: args) ret = Fun arg (MultiArgFun args ret)

public export
0 Fun_SOPLift : U_SOP tv -> Ty tv u -> VarTy tv -> Type
Fun_SOPLift [] r _ = ()
Fun_SOPLift (a :: b) r var = (Expr var (MultiArgFun a r), Fun_SOPLift b r var)

export
tabulate : {a : _} -> {u : U} -> {0 r : Ty tv u} -> (El_SOP a var -> Expr var r) -> Fun_SOPLift a r var
tabulate {a = []} f = ()
tabulate {a = [] :: xs} f = (f $ Z [], tabulate {a = xs} $ \sop => f (S sop))
tabulate {a = (z :: zs) :: xs} f =
  let rec = tabulate $ \sop => f (S sop)
      rec2 : Expr var z -> Fun_SOPLift (zs :: xs) r var = \x =>
        tabulate {a = zs :: xs} $ \sop => f $ case sop of
          Z p => Z (x :: p)
          S p => S p in
  (Lam _ (fst . rec2 . Var), rec)

export
index : {a : _} -> {u : U} -> {r : Ty tv u} -> Fun_SOPLift a r var -> (El_SOP a var -> Expr var r)
index {a = .([] :: xs)} (res, fs) (Z []) = res
index {a = _ :: xs} (res, fs) (S p) = index fs p
index {a = (y :: ys) :: xs} (f, fs) (Z (first :: rest)) =
  let app = App f first
      rec = index {a = ys :: xs} (app, fs) in
  rec (Z rest)
index {a = _ :: xs} (f, fs) (S p) = index fs p

%unbound_implicits off
export
genFun_SOPLift :
  {0 tv : Type} ->
  {a : U_SOP tv} ->
  {v : U} ->
  {r : Ty tv v} ->
  {0 u : U} ->
  {0 var : VarTy tv} ->
  Fun_SOPLift a r var ->
  Gen u var (Fun_SOPLift a r var)
genFun_SOPLift {a = []} () = pure ()
genFun_SOPLift {a = (ps :: a)} (f, fs) = [| (,) (gen f) (genFun_SOPLift fs) |]
%unbound_implicits on

export
{u : U} -> MonadJoin var (Gen u var) where
  join ma = MkGen $ \_, k => runGen $ do
    joinPoints <- genFun_SOPLift (tabulate (k . rep.backwards))
    a <- ma
    pure $ index joinPoints (rep.forwards a)
