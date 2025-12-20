module Prelude.Clone 
import Prelude.Copy


import public Builtin
import public Data.Linear.Notation
import public Data.Linear.Interface
import Data.Linear.Copies
import public Data.Linear.LVect
import Prelude
public export
data Clone : (1 ty : Type) -> {1 x : ty} -> Type where
  Cloned : (1 y : ty) -> (0 prf : y === x) -> Clone ty {x}


public export
mkClone : (1 x : a) -> Clone a {x}
mkClone x = Cloned x Refl
  
public export
unClone : (1 _ : Clone a {x}) -> a
unClone (Cloned y prf) = y
  
mutual 
    clone_succ : Copy a -> (k : Nat) -> (1 y : a) -> (1 z : a) -> {auto 0 _ : y = x} -> {auto 0 _ : z = x} -> LVect (S (S k)) (Clone a {x})
    clone_succ copy_inst k y z @{prfY} @{prfZ} = let 
        1 firstClone : Clone a {x=y} = mkClone y
        1 restClones : LVect (S k) (Clone a {x=z}) = clone k z
        1 firstClone' : Clone a {x} = rewrite sym prfY in firstClone
        1 restClones' : LVect (S k) (Clone a {x}) = rewrite sym prfZ in restClones
        in firstClone' :: restClones'
    public export
    clone : Copy a => (n : Nat) -> (1 x : a) -> LVect (S n) (Clone a {x})
    clone Z x = [mkClone x]
    clone (S k) x = copyWithEq' x (clone_succ %search k) 
public export
(.val) : (1 v : Clone a {x}) -> a
(.val) (Cloned y prf) = y
public export
0 (.prf) : (1 v : Clone a {x}) -> (v.val) === x
(.prf) (Cloned y prf) = prf
