||| https://andraskovacs.github.io/pdfs/2ltt_icfp24.pdf
||| https://github.com/AndrasKovacs/staged/blob/main/icfp24paper/supplement/agda-opsem/Interpreter.agda

module TwoLTT

import Control.Monad.Maybe
import Control.Monad.State
import Data.Morphisms.Iso
import Data.Vect
import Data.Vect.Quantifiers
import TwoLTT.Expr
import TwoLTT.Gen
import TwoLTT.JoinPoints
import TwoLTT.Types

%default total

0 CaseArms : {n : Nat} -> (0 ds : Vect n (Ty tyvar Val)) -> VarTy tyvar -> Ty tyvar u -> Vect n Type
CaseArms {n = 0} _ var mot = []
CaseArms {n = S n} ds var mot =
  (var _ (head ds) -> Expr var mot) :: CaseArms (tail ds) var mot

Case : {0 var : VarTy tv} -> {0 n : Nat} -> {ds : Vect n (Ty tv Val)} -> {0 motive : Ty tv u} -> (scrutinee : Expr var (Sum ds)) -> HVect (CaseArms ds var motive) -> Expr var motive
Case e [] {ds} =
  Absurd $ rewrite (sym $ invertVectZ ds) in e
Case e (arm :: arms) = Match e arm (\right => Case (Var right) arms)

-- https://github.com/AndrasKovacs/staged/blob/main/icfp24paper/supplement/haskell-cftt/CFTT/Improve.hs#L17
interface MonadGen Val var m => Improve (0 var : VarTy tyvar) (0 f : Ty tyvar Val -> Ty tyvar u) (0 m : Type -> Type) | m where
  up : {a : Ty _ Val} -> Expr var (f a) -> m (Expr var a)
  down : (a : Ty _ Val) -> m (Expr var a) -> Expr var (f a)

interface Split (0 a : Ty tyvar Val) where
  0 SplitTo : VarTy tyvar -> Type
  split : (0 var : VarTy _) -> Expr var a -> Gen Val var (SplitTo var)

data IdentityTag : Type where

Identity : Ty tyvar Val -> Ty tyvar Val
Identity a = Newtype IdentityTag a

Improve var Identity (Gen Val var) where
  up x = pure (Unwrap x)
  down a x = unGen x _ (Wrap _)

List : Ty tyvar Val -> Ty tyvar Val
List a = Fix (\list => Sum [One, Product [a, TyVar list]])

{a : Ty tyvar Val} -> Split (List a) where
  SplitTo var = Maybe (Expr var a, Expr var (List a))
  split _ as = MkGen $ \_, k =>
    Case (Unroll as %search) [
      \_ => k Nothing,
      \cons => k (Just (First (Var {ty = Product [a, List a]} cons), First (Rest (Var {ty = Product [a, List a]} cons))))
    ]

namespace TreeExample
  TreeF : Ty tyvar Val -> tyvar -> Ty tyvar Val
  TreeF a = (\tree => Sum [One, Product [a, TyVar tree, TyVar tree]])

  Tree : Ty tyvar Val -> Ty tyvar Val
  Tree a = Fix $ TreeF a

  leaf : {a : Ty tyvar Val} -> Expr var (Tree a)
  leaf = Roll (Left TT) %search

  node : {a : Ty tyvar Val} -> Expr var a -> (l, r : Expr var (Tree a)) -> Expr var (Tree a)
  node n l r =
    Roll (Right $ Left $ Prod n (Prod l $ Prod r TT)) %search

  data TreeSplit : (0 var : VarTy tyvar) -> Ty tyvar Val -> Type where
    Leaf : {0 a : Ty tyvar Val} -> TreeSplit var a
    Node : {0 a : Ty tyvar Val} -> Expr var a -> (l, r : Expr var (Tree a)) -> TreeSplit var a

  {a : Ty tyvar Val} -> Split (Tree a) where
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

  {a : Ty tyvar Val} -> Split (Maybe a) where
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

  fail : {0 f : Ty tv Val -> Ty tv u} -> Improve var f m => {a : Ty tv Val} -> Expr var (MaybeT f a)
  fail = down _ @{improveMaybeInstance} {m = MaybeT m} nothing

  MonadGen u var m => MonadGen u var (StateT s m) where
    liftGen = lift . liftGen

  [improveStateInstance]
  {f : Ty tv Val -> Ty tv Val} -> {s : Ty tv Val} -> Improve var f m => Improve var (StateT s f) (StateT (Expr var s) m) where
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

  fromInteger : (n : Integer) -> Expr v Nat
  fromInteger n = if n <= 0 then Roll (Left TT) %search else Roll (Right $ Left $ assert_total $ TreeExample.fromInteger (n - 1)) %search

  public export
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
            n <- join {var} $ case !(liftGen {var} $ split var $ the (Expr var (List Nat)) ns) of
              Nothing => pure n
              Just (n, ns) => do
                put ns
                pure n
            l <- up @{improveStateInstance @{improveMaybeInstance}} (App (Var f) l)
            r <- up @{improveStateInstance @{improveMaybeInstance}} (App (Var f) r)
            pure (node n l r)) Var
