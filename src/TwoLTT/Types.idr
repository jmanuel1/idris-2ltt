module TwoLTT.Types

import Data.String
import Data.Vect

%default total

public export
data U = Val | Comp

-- One weakness of this type system is that I have no notion of second-class
-- value types.
public export
data Ty : Type -> U -> Type where
  Fun :
    Ty var Val ->
    {u : U} -> -- unerased for call saturation
    Ty var u ->
    Ty var Comp
  Fix : (var -> Ty var Val) -> Ty var Val
  Product, Sum : (ds : Vect n $ Ty var Val) -> Ty var Val
  -- Only used for recursive value types, so supporting only value-type variables is fine
  TyVar : var -> Ty var Val
  Newtype : (tag : Type) -> Ty var u -> Ty var u

export
toString : Nat -> Ty Nat u -> String
toString n (Fun x y) = "(\{toString n x} -> \{toString n y})"
toString n (Fix f) = "fix (\\t\{show n} => \{toString (n + 1) (f n)})"
toString n t@(Product ds) = "(" ++ joinBy ", " ((\x => (toString n $ assert_smaller t x)) <$> toList ds) ++ ")"
toString n t@(Sum ds) = "(" ++ joinBy " | " ((\x => (toString n $ assert_smaller t x)) <$> toList ds) ++ ")"
toString n (TyVar x) = "t\{show x}"
toString n (Newtype tag x) = "newtype " ++ toString n x

public export
One, Zero : Ty tv Val
One = Product []
Zero = Sum []
