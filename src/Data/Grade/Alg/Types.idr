module Data.Grade.Alg.Types
import Data.Grade.Util.Relude
interface Alg a where
    0 AEq : a -> a -> Type 
    AEq = (===)
    0 ADecEq : (x : a) -> (y : a) -> Dec (AEq x y)
    1 toAlg : Int -@ a
    0 ALTE : a -> a -> Type 
    1 aadd : a -@ a -@ a
    1 amul : a -@ a -@ a
    1 amax : a -@ a -@ a 
    1 amin : a -@ a -@ a
    1 aone : a
    aone = toAlg 1
    1 azero : a
    azero = toAlg 0
    0 NonZero : a -> Type
    NonZero x = Not (AEq x azero)
    
