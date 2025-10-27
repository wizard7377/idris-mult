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
    ||| A custom function from QNat to QNat
    FFun : (1 f : ((1 x : QNat) -> QNat)) -> Form
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
minus : (1 k0 : QNat) -> (1 k1 : QNat) -> LMaybe QNat
minus k0 Zero = Just k0
minus (Succ k0) (Succ k1) = minus k0 k1
minus Zero (Succ k1) = seq k1 Nothing
private 
gte : (1 x : QNat) -> (1 y : QNat) -> Bool
gte Zero y = seq y False
gte (Succ x) Zero = seq x True
gte (Succ x) (Succ y) = gte x y

private 
ldiv' : (1 x : QNat) -> (1 y : QNat) -> LMaybe QNat
ldiv' x Zero = seq x $ Just Zero
ldiv' Zero y = seq y $ Just Zero
ldiv' x y = assert_total $ let 
  1 [x0] = x.clone 1
  1 [y0, y1] = y.clone 2
  in case Form.Types.minus &$ x0 &$ y0 of 
    Nothing => seq y1 $ Nothing 
    Just r => case ldiv' r &$ y1 of 
      Nothing => Nothing
      Just q => Just (Succ q)
private
diag : (1 x : QNat) -> LPair QNat QNat 
diag Zero = seq Zero $ (Zero # Zero)
diag n = assert_total $ let 
  1 [n0, n1] = n.clone 2
  in case (ldiv' n0.val) 2 of 
    Nothing => case (ldiv' n1.val) 3 of 
      Nothing => (Zero # Zero)
      Just q => let 
        (x' # y') = diag q
        in (x' # Succ y')
    Just q => seq n1 $ let 
      (x' # y') = diag q
      in (Succ x' # y')

 
public export 
pairing : QNat -@ (LPair QNat QNat)
pairing = diag

public export
FRange : (1 lo : QNat) -> (1 hi : QNat) -> Form
FRange lo hi = FMax (FMin (FVar) (FVal hi)) (FVal lo)
