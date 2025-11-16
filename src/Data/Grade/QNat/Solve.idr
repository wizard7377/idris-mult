module Data.Grade.QNat.Solve
import Builtin
import Prelude
import Data.Linear.Notation
import Data.Linear.Interface
  
import public Data.Grade.QNat.Types
import public Data.Grade.QNat.Ops
import public Data.Grade.QNat.Lemma
import public Data.Grade.Util.LPair
import Control.Relation
%default total

public export
0 QFin : QNat -> Type
QFin bound = Subset QNat (\n => LLTE n bound)

public export
weaken : (1 x : QFin n) -> (0 prf : LLTE n m) => QFin m
weaken (Element x prfX) @{prf} = Element x (transitive prfX prf)
