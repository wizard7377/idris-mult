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
    FApp : (1 op : FOp) -> Form -@ Form -@ Form
%name Form φ, ψ    

public export
LRange : (1 start : QNat) -> (1 end : QNat) -> LLTE start end => QList QNat 
LRange Zero Zero = Zero :: Nil
LRange Zero (Succ end) = Zero :: LRange Zero end
LRange (Succ start) (Succ end) = ?lrange_succ

public export
FAdd : Form -@ Form -@ Form
FAdd = FApp AddOp
public export
FMul : Form -@ Form -@ Form
FMul = FApp MulOp
public export
FRange : (1 start : QNat) -> (1 end : QNat) -> LLTE start end => Form
FRange start end = FVal (LRange start end)
public export
FVoid : Form
FVoid = FVal []

