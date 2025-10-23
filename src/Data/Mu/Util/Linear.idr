module Data.Mu.Util.Linear 

import Builtin
import Data.Linear.Notation
import Data.Linear.Interface
import Data.Linear.Copies
import Prelude

public export
record Eq3 (a : t) (b : t) (c : t) where
    constructor MkEq3
    eqAB : a === b
    eqAC : a === c
    eqBC : b === c

%hint public export
eqAB' : Eq3 a b c => a === b
eqAB' @{x} = let MkEq3 ab _ _ = x in ab
%hint public export
eqAC' : Eq3 a b c => a === c
eqAC' @{x} = let MkEq3 _ ac _ = x in ac
%hint public export
eqBC' : Eq3 a b c => b === c
eqBC' @{x} = let MkEq3 _ _ bc = x in bc
%hint public export
EqTree : Eq3 a b c => Eq3 c d e => Eq3 a d e
EqTree @{(MkEq3 ab ac bc)} @{(MkEq3 cd ce de)} = MkEq3 (trans ac cd) (trans ac ce) %search
public export  
data CloneOf : {a : Type} -> (x : a) -> Type where
  Cloned : (1 y : a) -> (1 z : a) -> Eq3 x y z -> CloneOf {a=a} x
%unsafe
%hint public export
0 seqEq : forall a, b. {x : a} -> {y : b} -> Consumable a => (seq x y) === y
seqEq = believe_me ()

%unsafe
%hint public export
0 extractEq : extract [x] === x
extractEq = believe_me ()

%unsafe
%hint public export
0 dupEq : Duplicable a => {x : a} -> {f : a -@ a -@ b} -> ((let (x1 :: xs) = duplicate x in f x1 (extract xs)) === (f x x))
dupEq = believe_me ()
             
public export
cloneWith : Duplicable a => (1 x : a) -> CloneOf x
cloneWith x = let 
    1 (y :: z) = duplicate x
  in Cloned y (extract z) (believe_me ())
