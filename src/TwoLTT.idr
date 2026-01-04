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
import TwoLTT.Monad.Identity
import TwoLTT.Monad.Improve
import TwoLTT.Monad.Maybe
import TwoLTT.Monad.State
import TwoLTT.Types

%default total



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
