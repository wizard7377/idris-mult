module Data.Grade.Logic.Contract
import Builtin
import Data.Linear.Notation
import Data.Grade.Util.LIso
import Data.Grade.Logic.Types
import Relude
import Control.Relation

||| Contractible types 
public export
record Contractible (0 a : Type) where 
    constructor Contract
    1 center' : a
    0 deform : {x : a} -> (x = center')

public export
contract : {0 a : Type} -> (1 x : a) => (0 prf : {0 y : a} -> (y === x) ) => Contractible a
contract @{x} @{prf} = Contract x prf
public export
(.center) : Contractible a -@ a
(.center) (Contract c d) = c

public export
Point : Contractible a =@ a 
Point @{c} = c.center
