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

public export
Duplicable a => Clone a where
    clone x = let 
        (y0 # y1) = splitAt (S Z) $ duplicate x
        in (extract y0 # extract y1)
public export
Consumable a => Drop a where
    drop = consume

public export 
dseq : Drop a => (1 x : a) -> (1 y : b) -> b
dseq x y = let x' = drop x in seq x' y

export 
infixl 9 #>>
public export
(#>>) : Drop a => (1 x : a) -> (1 y : b) -> b
(#>>) = dseq

public export
Drop a => Drop b => Drop (LPair a b) where
    drop (x # y) = x #>> y #>> () 
