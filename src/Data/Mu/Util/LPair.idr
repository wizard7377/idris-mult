module Data.Mu.Util.LPair
import Builtin
import Prelude.Basics
import Data.Linear.Notation
import Data.Mu.Util.Types
import Prelude.Types
import Prelude.Logic
%hide Basics.(.)

||| A linear existential type $∃ (x : ty). f x$
||| @ ty in the existential
||| @ f the predicate that must be satisfied, and the type of the value 
public export
record LExists {ty : Type} (f : (ty -> Type)) where
    constructor LEvidence
    ||| A certain `x`
    0 fst' : ty 
    ||| A value of `f x`
    1 snd' : f fst'

%inline %tcinline 
public export
0 (.fst) : (ex : LExists {ty} f) -> ty
(.fst) (LEvidence x y) = x
%inline %tcinline 
public export
(.snd) : (1 ex : LExists {ty} f) -> f (ex.fst)
(.snd) (LEvidence x y) = y
%inline %tcinline 
public export
0 fst : (ex : LExists {ty} f) -> ty
fst = (.fst)
%inline %tcinline 
public export
snd : (1 ex : LExists {ty} f) -> f (ex.fst)
snd = (.snd)
public export 
map : 
  {0 p : a -> Type} -> 
  {0 q : b -> Type} -> 
  {0 m : (a -> b)} -> 
  (1 f : forall x. p x -@ q (m x)) -> 
  (LExists p -@ LExists q)
map f (LEvidence x y) = LEvidence (m x) (f y)

public export
mapSnd : {0 p : a -> Type} -> {0 q : (a -> Type)} -> (1 f : forall x. p x -@ q x) -> (LExists p -@ LExists q)
mapSnd f (LEvidence x y) = LEvidence x (f y)
public export
compose : 
    {0 p : a -> Type} -> 
    {0 q : b -> Type} -> 
    {0 r : c -> Type} -> 
    {0 m : (a -> b)} -> 
    {0 n : (b -> c)} -> 
    (1 f : forall x. p x -@ q (m x)) -> 
    (1 g : forall y. q y -@ r (n y)) ->
    (LExists p -@ LExists r)
compose f g (LEvidence x y) = LEvidence (n (m x)) (g (f y))
