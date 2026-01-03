module Control.Function.FunExt.Axiom

%default total

export
0 funExt : {0 b : a -> Type} -> {0 f, g : (x : a) -> b x} -> ((x : a) -> f x = g x) -> f = g
funExt _ = believe_me (Refl {x = f})

export
0 funExt0 : {0 b : a -> Type} -> {0 f, g : (0 x : a) -> b x} -> ((x : a) -> f x = g x) -> f = g
funExt0 _ = believe_me (Refl {x = f})
