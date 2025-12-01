module Data.List.Erased

%default total

public export
data ErasedList : Type -> Type where
  Nil : ErasedList a
  (::) : (0 x : a) -> ErasedList a -> ErasedList a

%name ErasedList xs, ys, zs, ks, ls
%builtin Natural ErasedList

public export
(++) : ErasedList a -> ErasedList a -> ErasedList a
[] ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys

-- should be compiled to identity
public export
length : ErasedList a -> Nat
length [] = 0
length (_ :: xs) = S (length xs)
