module Main

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
  printLn (areCallsSaturated $ the (Expr {tv = ()} _ _) saturated)
where
  saturated : TypeOf TreeExample.f
  saturated = saturateCalls TreeExample.f
