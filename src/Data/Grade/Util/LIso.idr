module Data.Grade.Util.LIso 
import Control.Relation
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


public export
lIso : (f : (1 x : a) -> b) -> (g : (1 y : b) -> a) -> (forall x. (f (g x)) === x) => (forall y. (g (f y)) === y) => LIso a b
lIso f g @{iL} @{iR} = MkLIso (MkLIso' f g) ?h0 ?h1
public export 
lIso' : (f : (1 x : a) -> b) -> (g : (1 y : b) -> a) -> LIso' a b
lIso' f g = MkLIso' f g
public export
Reflexive Type LIso where
  reflexive = lIso (\x => x) (\y => y)  
