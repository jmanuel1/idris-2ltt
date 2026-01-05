||| https://andraskovacs.github.io/pdfs/2ltt_icfp24.pdf
||| https://github.com/AndrasKovacs/staged/blob/main/icfp24paper/supplement/agda-opsem/Interpreter.agda

module TwoLTT

import Control.Monad.Maybe
import Control.Monad.State
import Data.Morphisms.Iso
import Data.Vect
import Data.Vect.Quantifiers
import TwoLTT.Bool
import TwoLTT.Expr
import TwoLTT.Gen
import TwoLTT.JoinPoints
import public TwoLTT.List
import public TwoLTT.Monad.Identity
import TwoLTT.Monad.Improve
import public TwoLTT.Monad.Maybe
import public TwoLTT.Monad.State
import public TwoLTT.Nat
import public TwoLTT.Tree
import TwoLTT.Types

%default total

namespace TreeExample




  (==) : Expr var (Fun Nat (Fun Nat Bool))
  (==) = flip (LetRec _) Var $ \eq =>
    Lam _ $ \n => Lam _ $ \m =>
      unGen (do
        case (!(splitNat _ (Var n)), !(splitNat _ (Var m))) of
          (Nothing, Nothing) => pure true
          (Just n', Just m') => pure $ App (App (Var eq) (Var n')) (Var m')
          _ => pure false) _ id

  public export
  f : Expr var (Fun (Tree Nat) (StateT (List Nat) (MaybeT Identity) (Tree Nat)))
  f =
    LetRec _ (\f =>
      Lam (Tree Nat) $ \t => down _ $ do
        treeSplit <- liftGen {m = StateT (Expr var (List Nat)) (MaybeT (Gen Val var)), var} $ splitTree var $ Var t
        case treeSplit of
          Leaf => pure leaf
          Node n l r => do
            -- FIXME: Monad is determining parameter, yet I need to add {var}
            b <- liftGen {var} $ splitBool _ (App (App (==) $ Var n) 0)
            case b of
              True => lift nothing
              False => pure ()
            ns <- State.get
            n <- join {var} $ case !(liftGen {var} $ splitList var ns) of
              Nothing => pure $ Var n
              Just (n, ns) => do
                put $ Var ns
                pure $ Var n
            l <- up (App (Var f) $ Var l)
            r <- up (App (Var f) $ Var r)
            pure (node n l r)) Var
