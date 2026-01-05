module TwoLTT.Expr

import public Data.Vect
------ ^ for matching on constructors
import public Data.Vect.Quantifiers
import TwoLTT.Types
import public TwoLTT.Types.Sub
--     ^ for instance search

%default total

public export
0 VarTy : Type -> Type
VarTy tv = (0 u : U) -> Ty tv u -> Type

-- http://adam.chlipala.net/papers/PhoasICFP08/PhoasICFP08.pdf
public export
data Expr : VarTy tv -> Ty tv u -> Type where
  LetRec :
    {0 var : VarTy tv} ->
    {0 ty : Ty tv u} ->
    (a : Ty tv Comp) -> -- unerased for call saturation
    (t : var _ a -> Expr var a) ->
    (u : var _ a -> Expr var ty) ->
    Expr var ty
  Let :
    {0 var : VarTy tv} ->
    {u : U} -> -- unerased for eval
    (a : Ty tv u) -> -- unerased for call saturation
    {0 ty : Ty tv v} ->
    (t : Expr var a) ->
    (u : var _ a -> Expr var ty) ->
    Expr var ty
  -- Not having multi-way case in syntax so that Idris can see totality of Expr
  Absurd : Expr var (Sum []) -> {0 a : Ty tv u} -> Expr var a
  Match :
    {0 a : Ty tv u} ->
    {ds : Vect (S n) (Ty tv Val)} -> -- unerased for call saturation (eta expansion)
    Expr var (Sum ds) ->
    (var _ (head ds) -> Expr var a) ->
    (var _ (Sum $ tail ds) -> Expr var a) ->
    Expr var a
  Lam :
    {0 var : VarTy tv} ->
    (0 a : Ty tv Val) ->
    {u : U} -> -- unerased for eval
    {0 b : Ty tv u} ->
    (t : var _ a -> Expr var b) ->
    Expr var (Fun a b)
  Var : {0 var : VarTy tv} -> {0 ty : Ty tv u} -> var _ ty -> Expr var ty
  App :
    {a : Ty tv Val} -> -- unerased for call saturation
    {u : U} -> -- unerased for call saturation
    {b : Ty tv u} -> -- unerased for call saturation
    (f : Expr var (Fun a b)) ->
    (arg : Expr var a) ->
    Expr var b
  Left :
    {0 var : VarTy tv} ->
    {0 a : Ty tv Val} ->
    {0 b : Vect n (Ty tv Val)} ->
    Expr var a ->
    Expr var (Sum (a :: b))
  Right :
    {0 var : VarTy tv} ->
    {0 a : Ty tv Val} ->
    {0 b : Vect n (Ty tv Val)} ->
    Expr var (Sum b) ->
    Expr var (Sum (a :: b))
  TT : Expr var One
  Prod :
    {0 a : Ty tv Val} ->
    {0 b : Vect n (Ty tv Val)} ->
    Expr var a ->
    Expr var (Product b) ->
    Expr var (Product (a :: b))
  First :
    {0 a : Ty tv Val} ->
    {as : Vect n (Ty tv Val)} -> -- unerased for call saturation (eta expansion)
    Expr var (Product (a :: as)) ->
    Expr var a
  Rest :
    {a : Ty tv Val} -> -- unerased for call saturation (eta expansion)
    {0 as : Vect n (Ty tv Val)} ->
    Expr var (Product (a :: as)) ->
    Expr var (Product as)
  -- Represent coercions explicitly in syntax
  Roll :
    {unroll : Ty tv Val} -> -- unerased for call saturation (eta expansion)
    {0 f : tv -> Ty tv Val} ->
    Expr var unroll ->
    (0 sub : Sub {var = tv} f (Fix f) unroll) ->
    Expr var (Fix f)
  Unroll :
    {0 unroll : Ty tv Val} ->
    {f : tv -> Ty tv Val} -> -- unerased for call saturation (eta expansion)
    Expr var (Fix f) ->
    (0 sub : Sub {var = tv} f (Fix f) unroll) ->
    Expr var unroll

export
toString : Nat -> Expr {tv = Nat} (\_, _ => Nat) a -> String
toString n (LetRec x t u) = "let rec x\{show n} : \{toString 0 x} = \{toString (n + 1) (t n)} in \{toString (n + 1) (u n)}"
toString n (Let x t u) = "let x\{show n} : \{toString 0 x} = \{toString n t} in \{toString (n + 1) (u n)}"
toString n (Absurd x) = "absurd (\{toString n x})"
toString n (Match x f g) = "match \{toString n x} with x\{show n} => \{toString (n + 1) (f n)}; x\{show n} => \{toString (n + 1) (g n)}"
toString n (Lam x t) = "\\x\{show n} => \{toString (n + 1) (t n)}"
toString n (Var x) = "x\{show x}"
toString n (App f arg) = "(\{toString n f}) (\{toString n arg})"
toString n (Left x) = "Left (\{toString n x})"
toString n (Right x) = "Right (\{toString n x})"
toString n TT = "()"
toString n (Prod x y) = "(\{toString n x}, \{toString n y})"
toString n (First x) = "fst (\{toString n x})"
toString n (Rest x) = "snd (\{toString n x})"
toString n (Roll x sub) = "Roll (\{toString n x})"
toString n (Unroll x sub) = "unroll (\{toString n x})"

export
toStringWithoutTypes : Nat -> Expr (\_, _ => Nat) a -> String
toStringWithoutTypes n (LetRec x t u) = "let rec x\{show n} = \{toStringWithoutTypes (n + 1) (t n)} in \{toStringWithoutTypes (n + 1) (u n)}"
toStringWithoutTypes n (Let x t u) = "let x\{show n} = \{toStringWithoutTypes n t} in \{toStringWithoutTypes (n + 1) (u n)}"
toStringWithoutTypes n (Absurd x) = "absurd (\{toStringWithoutTypes n x})"
toStringWithoutTypes n (Match x f g) = "match \{toStringWithoutTypes n x} with x\{show n} => \{toStringWithoutTypes (n + 1) (f n)}; x\{show n} => \{toStringWithoutTypes (n + 1) (g n)}"
toStringWithoutTypes n (Lam x t) = "\\x\{show n} => \{toStringWithoutTypes (n + 1) (t n)}"
toStringWithoutTypes n (Var x) = "x\{show x}"
toStringWithoutTypes n (App f arg) = "(\{toStringWithoutTypes n f}) (\{toStringWithoutTypes n arg})"
toStringWithoutTypes n (Left x) = "Left (\{toStringWithoutTypes n x})"
toStringWithoutTypes n (Right x) = "Right (\{toStringWithoutTypes n x})"
toStringWithoutTypes n (Prod x y) = "(\{toStringWithoutTypes n x}, \{toStringWithoutTypes n y})"
toStringWithoutTypes n TT = "()"
toStringWithoutTypes n (First x) = "fst (\{toStringWithoutTypes n x})"
toStringWithoutTypes n (Rest x) = "snd (\{toStringWithoutTypes n x})"
toStringWithoutTypes n (Roll x sub) = "Roll (\{toStringWithoutTypes n x})"
toStringWithoutTypes n (Unroll x sub) = "unroll (\{toStringWithoutTypes n x})"

||| Check for equality of two expressions, ignoring types.
export
equal : Nat -> Expr (\_, _ => Nat) a -> Expr (\_, _ => Nat) b -> Bool
equal n (LetRec x t u) (LetRec y s v) = equal (n + 1) (t n) (s n) && equal (n + 1) (u n) (v n)
equal n (LetRec x t u) e2 = False
equal n (Let {u = u1} x t u) (Let {u = u2} y s v) = equal n t s && equal (n + 1) (u n) (v n)
equal n (Let x t u) e2 = False
equal n (Absurd x) (Absurd y) = equal n x y
equal n (Absurd x) e2 = False
equal n (Match x f g) (Match y f' g') = equal n x y && equal (n + 1) (f n) (f' n) && equal (n + 1) (g n) (g' n)
equal n (Match x f g) e2 = False
equal n (Lam x t) (Lam y s) = equal (n + 1) (t n) (s n)
equal n (Lam x t) e2 = False
equal n (Var x) (Var y) = x == y
equal n (Var x) e2 = False
equal n (App f arg) (App g arg') = equal n f g && equal n arg arg'
equal n (App f arg) e2 = False
equal n (Left x) (Left y) = equal n x y
equal n (Left x) e2 = False
equal n (Right x) (Right y) = equal n x y
equal n (Right x) e2 = False
equal n TT TT = True
equal n TT e2 = False
equal n (Prod x y) (Prod w z) = equal n x w && equal n y z
equal n (Prod x y) e2 = False
equal n (First x) (First y) = equal n x y
equal n (First x) e2 = False
equal n (Rest x) (Rest y) = equal n x y
equal n (Rest x) e2 = False
equal n (Roll x sub) (Roll y _) = equal n x y
equal n (Roll x sub) e2 = False
equal n (Unroll x sub) (Unroll y _) = equal n x y
equal n (Unroll x sub) e2 = False

public export
0 Expr' : Ty tv u -> Type
Expr' ty = forall var. Expr var ty

public export
0 CaseArms : {n : Nat} -> (0 ds : Vect n (Ty tyvar Val)) -> VarTy tyvar -> Ty tyvar u -> Vect n Type
CaseArms {n = 0} _ var mot = []
CaseArms {n = S n} ds var mot =
  (var _ (head ds) -> Expr var mot) :: CaseArms (tail ds) var mot

export
Case : {0 var : VarTy tv} -> {0 n : Nat} -> {ds : Vect n (Ty tv Val)} -> {0 motive : Ty tv u} -> (scrutinee : Expr var (Sum ds)) -> HVect (CaseArms ds var motive) -> Expr var motive
Case e [] {ds} =
  Absurd $ rewrite (sym $ invertVectZ ds) in e
Case e (arm :: arms) = Match e arm (\right => Case (Var right) arms)
