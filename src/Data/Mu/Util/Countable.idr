module Data.Mu.Util.Countable
import Prelude.Types
import Data.Linear.LNat
public export
interface Countable (ty : Type) where
    0 count : ty -> LNat
    0 index : LNat -> ty

public export
Countable LNat where
    count n = n
    index n = n
