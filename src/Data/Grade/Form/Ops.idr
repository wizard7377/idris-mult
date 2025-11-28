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
public export
0 Solve : Rel [Form, QNat]
Solve FVar n = qseq n ()
Solve (FVal m) n = QElem n m
Solve (FApp op p q) n = Exists (Duple QNat QNat) (\(For a b) => (Duple (Duple (Solve p a) (Solve q b)) (n = runOp op a b)))

public export 
0 Unify : Rel [Form, Form]
Unify p q = (forall n. (Solve p n -@ Solve q n))

public export
0 Equiv : Rel [Form, Form]
Equiv p q = (Duple (Unify p q) (Unify q p))
