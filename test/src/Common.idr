module Common 

import public Data.Grade
import public Data.Grade.QNat
import public Data.Linear.Notation
import public Data.Grade.Set
public export
assertEq : Show a => Eq a => a -> IO a -> IO Bool
assertEq expected actual = do 
    result <- actual
    if (expected == result) then (putStrLn ("passed") >> pure True) else (putStrLn $ " failed: expected " ++ show expected ++ ", got " ++ show result) >> pure False
