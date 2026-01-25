module Data.Grade.QNat.Solve
import Builtin
import Prelude
import Data.Linear.Notation
import Data.Linear.Interface
  
import public Data.Grade.QNat.Types
import public Data.Grade.QNat.Ops
import public Data.Grade.QNat.Lemma
import public Data.Grade.Logic
import Control.Relation
%default total

public export
0 QFin : QNat -> Type
QFin bound = Sigma QNat (\n => LLTE n bound)

public export
weaken : (1 x : QFin n) -> (0 prf : LLTE n m) => QFin m
weaken (For x prfX) @{prf} = For x (transitive prfX prf)
