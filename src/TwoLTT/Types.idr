module TwoLTT.Types

import Data.Vect

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
  Newtype : (0 tag : Type) -> Ty var u -> Ty var u

public export
One, Zero : Ty tv Val
One = Product []
Zero = Sum []
