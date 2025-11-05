module Data.Grade.Alg.Types
import Data.Linear.Notation
import Prelude
import Decidable.Equality
public export
interface Alg a where
    
    0 AEq : a -> a -> Type 
    AEq = (===)
    0 aeq : (x : a) -> (y : a) -> Dec (AEq x y)
    toAlg : Integer -> a
    0 ALTE : a -> a -> Type 
    1 aadd : a -@ a -@ a
    1 amul : a -@ a -@ a
    1 amax : a -@ a -@ a 
    1 amin : a -@ a -@ a 
public export
interface Alg a => Pred a where 
  0 NonZero : a -> Type
  0 nonZero : (x : a) -> Dec (NonZero x)
  1 pred : (1 x : a) -> NonZero x => a
  
public export
Alg a => Num a where 
    (+) x y = aadd x y
    (*) x y = amul x y
    fromInteger x = toAlg (cast x)

