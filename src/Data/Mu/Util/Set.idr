module Data.Mu.Util.Set
import Prelude
%default total

public export
data Set : (u : Type) -> Type where 
  Phi : ((0 x : u) -> Type) -> Set u

%inline
public export
proj : {u : Type} -> (s : Set u) -> (0 x : u) -> Type
proj (Phi p) = p
%hint 
public export
All : Set u
All = Phi (\_ => ())

public export
Element : {u : Type} -> (s : Set u) -> (0 x : u) -> Type
Element {u = u} (Phi p) x = p x

%hint 
public export
TrivialIn : {u : Type} -> (x : u) -> Element All x
TrivialIn x = ()
public export 
Conj : Set u -> Set u -> Set u
Conj (Phi p) (Phi q) = Phi (\x => (p x, q x))
public export
Disj : Set u -> Set u -> Set u
Disj (Phi p) (Phi q) = Phi (\x => Either (p x) (q x))
