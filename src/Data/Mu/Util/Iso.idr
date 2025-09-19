module Data.Mu.Util.Iso 
import Prelude
import Data.Linear.Notation
public export
record LIso (a : Type) (b : Type) where 
    constructor MkLIso
    lto   : a -@ b
    lfrom : b -@ a
