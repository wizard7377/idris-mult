module Prelude.Linear 
import Data.Linear.Notation
import Builtin
import Data.Linear.Interface
import Prelude.Types
import Prelude.Num
public export
interface Clone (0 t : Type) where 
    constructor MkClone
    clone : (1 x : t) -> (LPair t t)
public export
interface Drop (0 t : Type) where 
    constructor MkDrop
    drop : (1 x : t) -> ()
