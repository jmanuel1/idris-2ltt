module Main

import Data.DPair
import TwoLTT
import TwoLTT.CallSat
import TwoLTT.Expr
import TwoLTT.Types

0 TypeOf : {a : Type} -> a -> Type
TypeOf _ = a

main : IO ()
main = do
  putStrLn (toString 0 TreeExample.f)
  putStrLn (toString 0 $ saturated)
  let _ = Monoid.Additive
  putStrLn $ case (areCallsSaturated $ the (Expr {tv = ()} _ _) saturated) of
    Left (NotSatCall e) => "call not saturated: " ++ (Expr.toStringWithoutTypes 0 $ e.snd.snd.snd)
    Left (NotEtaLong e) => "defn not eta long: " ++ (Expr.toStringWithoutTypes 0 $ e.snd.snd.snd)
    Right () => "saturated"
where
  saturated : TypeOf TreeExample.f
  saturated = saturateCalls TreeExample.f
