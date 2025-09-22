module Data.Mu.Util.LIso 

import Builtin
public export
record LIso' (a : Type) (b : Type) where
    constructor MkLIso'
    to   : (1 x : a) -> b
    from : (1 y : b) -> a

public export
record LIso (a : Type) (b : Type) where
    constructor MkLIso
    iso : LIso' a b
    0 iL : {x : a} -> iso.from (iso.to x) === x
    0 iR : {y : b} -> iso.to (iso.from y) === y
