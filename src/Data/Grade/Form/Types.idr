module Data.Grade.Form.Types
import Data.Linear.Notation
import Data.Grade.Util.Linear
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
data Form : (n : QNat) -> Type where 
    ||| The argument variable
    FVar : (1 n : QNat) -> Form (Succ n)
    ||| Value obtained by splitting the argument at n
    FSplit : Form a -@ Form b -@ Form (a + b)
    ||| A constant value
    FVal : (1 n : QNat) -> Form 0
    ||| Map one formula through another one, ie, g(f(x))
    FApp : (1 g : Form a) -> (1 f : Form b) -> Form (lmax a b)
    ||| Add the result of f with the result of g
    FAdd : (1 x : Form a) -> (1 y : Form b) -> Form (lmax a b)
    ||| Multiply the result of f with the result of g
    FMul : (1 x : Form a) -> (1 y : Form b) -> Form (lmax a b)
    ||| Take the minimum between the result of f and g
    FMin : (1 x : Form a) -> (1 y : Form b) -> Form (lmax a b)
    ||| Take the maximum between the result of f and g
    FMax : (1 x : Form a) -> (1 y : Form b) -> Form (lmax a b)
    
  
export 
infixl 4 #+#
export 
infixl 5 #*#
export 
infixr 9 #$#
export 
prefix 9 ###

public export
(#$#) : (1 f : Form a) -> (1 x : Form b) -> Form (lmax a b)
f #$# x = FApp f x
public export
(#+#) : (1 f : Form a) -> (1 g : Form b) -> Form (lmax a b)
f #+# g = FAdd f g
public export
(#*#) : (1 f : Form a) -> (1 g : Form b) -> Form (lmax a b)
f #*# g = FMul f g
public export
(###) : QNat -@ Form 0
(###) n = FVal n

public export
AForm : Type 
AForm = Exists QNat Form
public export
Num AForm where 
    (Evidence w x) + (Evidence v y) = Evidence (lmax w v) (x #+# y)
    (Evidence w x) * (Evidence v y) = Evidence (lmax w v) (x #*# y)
    fromInteger n = exists $ FVal (fromInteger n)
public export
Semigroup AForm where 
    (Evidence w f) <+> (Evidence v x) = Evidence (lmax w v) (f #$# x)
public export
FRange : (1 lo : QNat) -> (1 hi : QNat) -> AForm
FRange lo hi = exists $ FMax (FMin (FVar 0) (FVal hi)) (FVal lo)

  
