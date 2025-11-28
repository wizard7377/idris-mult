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
import Data.Grade.Logic
import Prelude
import Control.Relation
import Relude
%default total
public export
data QList : Type -> Type where
  Nil : QList a
  (::) : (1 x : a) -> (1 xs : QList a) -> QList a
  
public export
Consumable a => Consumable (QList a) where 
    consume Nil = ()
    consume (x :: xs) = seq x (consume xs)
public export
Copy a => Copy (QList a) where 
    copy f Nil = f Nil Nil
    copy f (x :: xs) = copy (\x, y => copy (\xs, ys => f (x :: xs) (y :: ys)) xs) x
    copy_eq = ?copy_qlist_eq

public export
data QElem : (1 x : a) -> (1 xs : QList a) -> Type where
  QHere : QElem x (x :: xs)
  QThere : QElem x xs -> QElem x (y :: xs)

%hint 
export 
QElemRefl : (0 x : a) -> (0 y : a) -> QElem x (y :: []) => x === y
QElemRefl x x @{QHere} = Refl
%hint 
export 
HintEq : (0 _ : x === y) => QElem x (y :: ys)   
HintEq @{prf} = rewrite prf in QHere
  
  
public export
Uninhabited (QElem x Nil) where 
    uninhabited prf = case prf of {}
public export
Consumable (QElem x xs) where 
    consume (QHere) = ()
    consume (QThere prf) = consume prf
public export  
data FOp = AddOp | MulOp

public export
Consumable FOp where 
    consume AddOp = ()
    consume MulOp = ()
public export
Copy FOp where 
    copy f AddOp = f AddOp AddOp
    copy f MulOp = f MulOp MulOp
    copy_eq = ?copy_fop_eq
public export 
runOp : FOp -@ QNat -@ QNat -@ QNat
runOp AddOp = ladd 
runOp MulOp = lmul
||| A formula for an linear natural number, with exactly one variable
||| Can easily be evaluated with 'feval'
public export
data Form : Type where 
    ||| The argument variable
    FVar : Form
    ||| A constant value
    FVal : QList QNat -@ Form
    FAdd : Form -@ Form -@ Form
    FMul : Form -@ Form -@ Form


%name Form p,q,r,s,p',q',r',s',p0,q0,r0,s0,p1,q1,r1,s1  
public export
LRange : (1 start : QNat) -> (1 end : QNat) -> LLTE start end => QList QNat 
LRange Zero Zero = Zero :: Nil
LRange Zero (Succ end) = Zero :: LRange Zero end
LRange (Succ start) (Succ end) = ?lrange_succ

public export
FRange : (1 start : QNat) -> (1 end : QNat) -> LLTE start end => Form
FRange start end = FVal (LRange start end)
public export
FVoid : Form
FVoid = FVal []
public export
FUnit : Form
FUnit = FVar

consumeForm : Form -@ ()
consumeForm FVar = () 
consumeForm (FVal ns) = consume ns
consumeForm (FAdd p q) = (seq (consumeForm p) (consumeForm q))
consumeForm (FMul p q) = (seq (consumeForm p) (consumeForm q))
public export
Consumable Form where 
  consume = consumeForm

public export
Copy Form where 
  copy f FVar = f FVar FVar
  copy f (FVal ns) = copy (\ns1, ns2 => f (FVal ns1) (FVal ns2)) ns
  copy f (FAdd p q) = copy (\p1, p2 => copy (\q1, q2 => f (FAdd p1 q1) (FAdd p2 q2)) q) p
  copy f (FMul p q) = copy (\p1, p2 => copy (\q1, q2 => f (FMul p1 q1) (FMul p2 q2)) q) p
  copy_eq = ?copy_form_eq
  
