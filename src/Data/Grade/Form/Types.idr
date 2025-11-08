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
data Form : Type where 
    ||| The argument variable
    FVar : Form 
    ||| A constant value
    FVal : (1 n : QNat) -> Form 
    ||| Map one formula through another one, ie, g(f(x))
    FApp : (1 g : Form) -> (1 f : Form) -> Form
    ||| Add the result of f with the result of g
    FAdd : (1 x : Form) -> (1 y : Form) -> Form
    ||| Multiply the result of f with the result of g
    FMul : (1 x : Form) -> (1 y : Form) -> Form
    ||| Take the minimum between the result of f and g
    FMin : (1 x : Form) -> (1 y : Form) -> Form
    ||| Take the maximum between the result of f and g
    FMax : (1 x : Form) -> (1 y : Form) -> Form
    ||| Left projection of a pair
    FLeft : (1 f : Form) -> Form
    ||| Right projection of a pair
    FRight : (1 f : Form) -> Form
  
export 
infixl 4 #+#
export 
infixl 5 #*#
export 
infixr 9 #$#
export 
prefix 9 ###

public export
(#$#) : (1 f : Form) -> (1 x : Form) -> Form
f #$# x = FApp f x
public export
(#+#) : (1 f : Form) -> (1 g : Form) -> Form
f #+# g = FAdd f g
public export
(#*#) : (1 f : Form) -> (1 g : Form) -> Form
f #*# g = FMul f g
public export
(###) : QNat -@ Form
(###) n = FVal n

public export
Num Form where 
    x + y = (x #+# y)
    x * y = (x #*# y)
    fromInteger n = FVal (fromInteger n)
public export
Semigroup Form where 
    f <+> x = FApp f x
public export
Monoid Form where 
    neutral = FVar
public export
FRange : (1 lo : QNat) -> (1 hi : QNat) -> Form
FRange lo hi = FMax (FMin (FVar) (FVal hi)) (FVal lo)

  
export 
infixl 0 <.>
public export
(<.>) : (1 f : Form) -> (1 g : Form -@ Form) -> Form
f <.> g = FApp f (g FVar)
