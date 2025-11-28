module Data.Grade.Form.Ops
import Data.Grade.Form.Types
import Data.Linear.Notation
import Data.Grade.Util.Linear
import Data.Linear.Interface
import Data.Grade.QNat
import Prelude.Num
import Builtin
import Prelude.Types
import Data.Linear.LMaybe
import Data.Grade.Logic
import Prelude
import Data.Rel
import Data.Vect
import Data.Fun
%inline %tcinline
public export
0 Solve : Rel [Form, QNat]
Solve FVar n = ()
Solve (FVal m) n = QElem n m
Solve (FAdd p q) n = Exists2 QNat QNat (\m1, m2 => Subset2 (Solve p m1) (Solve q m2) (\_, _ => (n === (m1 + m2))))
Solve (FMul p q) n = Exists QNat (\m => Subset (Solve p m) (\_ => SolveN m q n))
  where 
    SolveN : QNat -> Rel [Form, QNat] 
    SolveN (Succ k) p n = Exists2 QNat QNat (\x, y => All [(Solve p x), (SolveN k p y), (n === (x * y))])
    SolveN Zero p n = (n === Zero)
public export 
0 Unify : Rel [Form, Form]
Unify p q = (forall n. (Solve p n -@ Solve q n))

public export
0 Equiv : Rel [Form, Form]
Equiv p q = (Duple (Unify p q) (Unify q p))

public export
infix 0 <:, :>, :~:, <?, ?>

%inline %tcinline public export
0 (<:) : Rel [QNat, Form]
x <: p = Solve p x
%inline %tcinline public export
0 (:>) : Rel [Form, QNat]
p :> x = Solve p x
%inline %tcinline public export
0 (:~:) : Rel [Form, Form]
p :~: q = Equiv p q
%inline %tcinline public export
0 (<?) : Rel [Form, Form]
p <? q = Unify p q
%inline %tcinline public export
0 (?>) : Rel [Form, Form]
p ?> q = Unify q p
