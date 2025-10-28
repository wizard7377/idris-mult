module Data.Grade.Util.Countable
import Prelude.Types
import Data.Grade.QNat
public export
interface Countable (ty : Type) where
    0 count : ty -> QNat
    0 index : QNat -> ty

public export
Countable QNat where
    count n = n
    index n = n
