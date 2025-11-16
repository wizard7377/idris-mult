module Tests.Eval
  
import Prelude
import Data.Mu
import Data.Grade.Form
import Data.Grade.QNat
import Common
private 
formula1 : Form 
formula1 = FApp (FMul' FVar' (FVal' 0)) (FMul' FVar' FVar')

private 
Show QNat where 
    show Zero = "0"
    show (Succ k) = "S " ++ show k
private 
Eq QNat where 
    Zero == Zero = True
    (Succ k1) == (Succ k2) = k1 == k2
    _ == _ = False
private 
res1 : QNat 
res1 = Eval' formula1 4
public export
evalTest : IO ()
evalTest = do 
  _ <- assertEq (the QNat 0) (pure res1)
  pure ()
