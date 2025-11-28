module Data.Grade.Logic.Contract
import Builtin
import Data.Linear.Notation
import Data.Grade.Util.LIso
import Data.Grade.Logic.Types
import Relude
import Control.Relation

||| Contractible types 
export
record Contractible (0 a : Type) where 
    constructor Contract
    1 center' : a
    0 deform' : {x : a} -> (x = center')
