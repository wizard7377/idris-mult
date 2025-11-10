module Data.Grade.Form.Types
import Data.Linear.Notation
import Data.Grade.Util.Linear
import Data.Nat
import Data.Linear.Interface
import Data.Grade.QNat
import Prelude.Num
import Builtin
import Prelude.Types
import Data.Linear.LVect
import Data.Linear.LMaybe
import Data.Grade.Util.LPair
import Prelude
import Control.Relation
||| A formula for an linear natural number, with exactly one variable
||| Can easily be evaluated with 'feval'
public export
data Form' : Nat -> Type where 
    ||| The argument variable
    FVar : Form' 1
    ||| A constant value
    FVal : (1 n : QNat) -> Form' 0
    ||| Add the result of f with the result of g
    FAdd : {1 a : Nat} -> (1 x : Form' a) -> (1 y : Form' b) -> Form' (a + b)
    ||| Multiply the result of f with the result of g
    FMul : {1 a : Nat} -> (1 x : Form' a) -> (1 y : Form' b) -> Form' (a + b)
    ||| Take the minimum between the result of f and g
    FMin : {1 a : Nat} -> (1 x : Form' a) -> (1 y : Form' b) -> Form' (a + b)
    ||| Take the maximum between the result of f and g
    FMax : {1 a : Nat} -> (1 x : Form' a) -> (1 y : Form' b) -> Form' (a + b)
  
export 
infixl 4 #+#
export 
infixl 5 #*#
export 
infixr 9 #$#
export 
prefix 9 ###

public export
(#+#) : {1 a : Nat} -> (1 f : Form' a) -> (1 g : Form' b) -> Form' (a + b)
f #+# g = FAdd f g
public export
(#*#) : {1 a : Nat} -> (1 f : Form' a) -> (1 g : Form' b) -> Form' (a + b)
f #*# g = FMul f g
public export
(###) : QNat -@ Form' 0
(###) n = FVal n
public export
record Form where
    constructor Over 
    1 vars : Nat
    1 form : Form' vars
  
public export
over : {1 n : Nat} -> Form' n -> Form
over {n} f = Over n f
public export
Num Form where 
    fromInteger n = Over 0 (FVal (fromInteger n))
    (Over n f) + (Over m g) = Over (n + m) (f #+# g)
    (Over n f) * (Over m g) = Over (n + m) (f #*# g)
public export
FRange : (1 lo : QNat) -> (1 hi : QNat) -> Form' n -> Form' n
FRange lo hi f = FMax (FVal lo) (FMin (FVal hi) f) 
  
