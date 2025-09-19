module Data.Mu.Util.Part
import Prelude
%default total

public export
data Part : (u : Type) -> Type where 
  Phi : ((0 x : u) -> Type) -> Part u

%inline
public export
proj : {u : Type} -> (s : Part u) -> (0 x : u) -> Type
proj (Phi p) = p
%hint 
public export
All : Part u
All = Phi (\_ => ())

public export
Element : {u : Type} -> (s : Part u) -> (0 x : u) -> Type
Element {u = u} (Phi p) x = p x

%hint 
public export
TrivialIn : {u : Type} -> (x : u) -> Element All x
TrivialIn x = ()
public export 
Conj : Part u -> Part u -> Part u
Conj (Phi p) (Phi q) = Phi (\x => (p x, q x))
public export
Disj : Part u -> Part u -> Part u
Disj (Phi p) (Phi q) = Phi (\x => Either (p x) (q x))
