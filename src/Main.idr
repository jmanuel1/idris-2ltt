module Main

import TwoLTT
import TwoLTT.CallSat
import TwoLTT.Expr
import TwoLTT.Types

main : IO ()
main = do
  putStrLn (toString 0 TreeExample.f)
  putStrLn (toString 0 $ saturateCalls TreeExample.f)
