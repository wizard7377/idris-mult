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
import public Data.Grade.Logic.QList
%default total

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
    FTop : Form
    FBot : Form
    ||| A constant value
    FVal : QNat -@ Form
    FAlt : Form -@ Form -@ Form
    FAdd : Form -@ Form -@ Form
    FMul : Form -@ Form -@ Form


%name Form p,q,r,s,p',q',r',s',p0,q0,r0,s0,p1,q1,r1,s1  
public export
LRange : (1 start : QNat) -> (1 end : QNat) -> LLTE start end => QList QNat 
LRange Zero Zero = Zero :: Nil
LRange Zero (Succ end) = Zero :: LRange Zero end
LRange (Succ start) (Succ end) = ?lrange_succ

public export
FOne : (ps : QList Form) -> Form
FOne (p :: ps) = FAlt p (FOne ps)
FOne [] = FBot
public export
FVoid : Form
public export
FUnit : Form
FUnit = FTop
mutual 
    consumeForm : Form -@ ()
    consumeForm FTop = () 
    consumeForm FBot = () 
    consumeForm (FVal ns) = consume ns
    consumeForm (FAdd p q) = (seq (consumeForm p) (consumeForm q))
    consumeForm (FMul p q) = (seq (consumeForm p) (consumeForm q))
    consumeForm (FAlt p q) = (seq (consumeForm p) (consumeForm q))
    public export
    Consumable Form where 
        consume = consumeForm

public export
Copy Form where 
    copy f FTop = f FTop FTop
    copy f (FVal ns) = copy (\ns1, ns2 => f (FVal ns1) (FVal ns2)) ns
    copy f (FAlt p q) = assert_total $ copy (\p1, p2 => copy (\q1, q2 => f (FAlt p1 q1) (FAlt p2 q2)) q) p
    copy f FBot = f FBot FBot
    copy f (FAdd p q) = assert_total $ copy (\p1, p2 => copy (\q1, q2 => f (FAdd p1 q1) (FAdd p2 q2)) q) p
    copy f (FMul p q) = assert_total $ copy (\p1, p2 => copy (\q1, q2 => f (FMul p1 q1) (FMul p2 q2)) q) p
    copy_eq = believe_me ()
  
