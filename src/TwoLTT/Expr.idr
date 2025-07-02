module TwoLTT.Expr

import public Data.Vect
------ ^ for matching on constructors
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
  LetRec : {0 var : VarTy tv} -> {0 ty : Ty tv u} -> (0 a : Ty tv Comp) -> (t : var _ a -> Expr var a) -> (u : var _ a -> Expr var ty) -> Expr var ty
  Let :
    {0 var : VarTy tv} ->
    {u : U} -> -- unerased for eval
    (0 a : Ty tv u) ->
    {0 ty : Ty tv v} ->
    (t : Expr var a) ->
    (u : var _ a -> Expr var ty) ->
    Expr var ty
  -- Not having multi-way case in syntax so that Idris can see totality of Expr
  Absurd : Expr var (Sum []) -> {0 a : Ty tv u} -> Expr var a
  Match :
    {0 a : Ty tv u} ->
    {0 ds : Vect (S n) (Ty tv Val)} ->
    Expr var (Sum ds) ->
    (var _ (head ds) -> Expr var a) ->
    (var _ (Sum $ tail ds) -> Expr var a) ->
    Expr var a
  Lam : {0 var : VarTy tv} -> (0 a : Ty tv Val) -> {0 b : Ty tv u} -> (t : var _ a -> Expr var b) -> Expr var (Fun a b)
  Var : {0 var : VarTy tv} -> {0 ty : Ty tv u} -> var _ ty -> Expr var ty
  App : {0 a : Ty tv Val} -> {0 b : Ty tv u} -> (f : Expr var (Fun a b)) -> (arg : Expr var a) -> Expr var b
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
    {0 as : Vect n (Ty tv Val)} ->
    Expr var (Product (a :: as)) ->
    Expr var a
  Rest :
    {0 a : Ty tv Val} ->
    {0 as : Vect n (Ty tv Val)} ->
    Expr var (Product (a :: as)) ->
    Expr var (Product as)
  -- Represent coercions explicitly in syntax
  Wrap : (0 tag : Type) -> {0 a : Ty tv u} -> Expr var a -> Expr var (Newtype tag a)
  Unwrap : {0 a : Ty tv u} -> Expr var (Newtype tag a) -> Expr var a
  Roll : {0 unroll : Ty tv Val} -> {0 f : tv -> Ty tv Val} -> Expr var unroll -> (0 sub : Sub {var = tv} f (Fix f) unroll) -> Expr var (Fix f)
  Unroll : {0 unroll : Ty tv Val} -> {0 f : tv -> Ty tv Val} -> Expr var (Fix f) -> (0 sub : Sub {var = tv} f (Fix f) unroll) -> Expr var unroll

public export
0 Expr' : Ty tv u -> Type
Expr' ty = forall var. Expr var ty
