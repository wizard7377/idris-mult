module Prelude.Clone
import Prelude.Copy


import public Builtin
import public Data.Linear.Notation
import public Data.Linear.Interface
import Data.Linear.Copies
import public Data.Linear.LVect
import Prelude
public export
data Cloned : (1 ty : Type) -> {1 x : ty} -> Type where
  MkCloned : (1 y : ty) -> (0 prf : y === x) -> Cloned ty {x}


public export
mkCloned: (1 x : a) -> Cloned a {x}
mkCloned x = MkCloned x Refl
  
public export
unCloned : (1 _ : Cloned a {x}) -> a
unCloned (MkCloned y prf) = y
  
mutual 
    clone_succ : Copy a -> (k : Nat) -> (1 y : a) -> (1 z : a) -> {auto 0 _ : y = x} -> {auto 0 _ : z = x} -> LVect (S (S k)) (Cloned a {x})
    clone_succ copy_inst k y z @{prfY} @{prfZ} = let 
        1 firstCloned: Cloned a {x=y} = mkCloned y
        1 restClones : LVect (S k) (Cloned a {x=z}) = clone k z
        1 firstClone' : Cloned a {x} = rewrite sym prfY in firstCloned
        1 restClones' : LVect (S k) (Cloned a {x}) = rewrite sym prfZ in restClones
        in firstClone' :: restClones'
    public export
    clone : Copy a => (n : Nat) -> (1 x : a) -> LVect (S n) (Cloned a {x})
    clone Z x = [mkCloned x]
    clone (S k) x = copyWithEq' x (clone_succ %search k) 
public export 
(.clone) : Copy a => (1 x : a) -> (n : Nat) -> LVect (S n) (Cloned a {x})
(.clone) x n = clone n x
public export
(.val) : (1 v : Cloned a {x}) -> a
(.val) (MkCloned y prf) = y
public export
0 (.prf) : (1 v : Cloned a {x}) -> (v.val) === x
(.prf) (MkCloned y prf) = prf
%hint
public export 
0 CloneEq : {a : Cloned t {x}} -> {b : Cloned t {x}} -> a.val === b.val
CloneEq {a=(MkCloned y0 prf0)} {b=(MkCloned y1 prf1)} = trans prf0 (sym prf1)

public export
(.use) : forall t. {0 x : t} -> {0 p : t -> Type} -> (1 c : Cloned t {x}) -> (1 f : (1 y : t) -> p y) -> p x
v.use f = rewrite sym v.prf in f v.val

public export
Drop a => Drop (Cloned a {x}) where
    drop (MkCloned y prf) = drop y
public export
Copy a => Copy (Cloned a {x}) where
  copy = ?copy_proof
