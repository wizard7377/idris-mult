module Data.Mu.Lawful.Types

import public Prelude.Types
import Prelude.Ops
import Prelude.Num
import Prelude.Basics
import Data.Linear.LVect
import Data.Mu.Util.Image
import Data.Linear.LList
import Data.Mu.Simple.Classes
import Data.Linear.Notation
import Data.Nat as Data.Nat
import Data.Linear.LNat
import Control.Function
import Prelude.Cast
import Builtin
import PrimIO 
import Data.Mu.Util.Part
%auto_lazy off
%default total
public export
data Arena : {0 n : Nat} -> (t : Type) -> Type where
  MkArena : AnyPtr -> Arena {n} t
mutual
    ||| The `Mu` type, represents a graded multiplicity container. 
    ||| Uses induction to allow for a certain number of linear bindings.
    ||| Note that this does *not* work for the zero modality, as `0` acts more as a modality than a quantity
    |||
    ||| @ n The number of linear bindings of `t` to keep 
    ||| @ t The type of the elements in the container
    public export
    data M : (0 n : Nat) -> (t : Type) -> Type where
        ||| The inductive case, adds one more linear binding of `t`
        ||| Written in the paper as `x ⊗ xs` 
        MS : {0 n : Nat} -> {0 t : Type} -> (1 x : t) -> (1 xs : (M n t)) -> {auto 0 prf : Extends x xs} -> M (S n) t
        ||| The base case, represents zero linear bindings of `t`
        ||| Written in the paper as `⋄`
        MZ : {0 t : Type} -> M Z t
    ||| A proof that an element `x` may extend `M n a`, as it is equal to each element
    public export 
    data Extends : {0 a : Type} -> {n : Nat} -> (x : a) -> (xs : M n a) -> Type where 
        [search x xs]
        ||| The base case, everything extends the empty container
        ExtendsZero : {0 a : Type} -> {0 x : a} -> Extends x MZ
        
        ||| The inductive case, `x` extends `MS y ys` if `x` is equal to `y` and `x` extends `ys`
        ExtendsSucc : {0 n : Nat} -> {0 a : Type} -> {0 x, y : a} -> {0 z : M n a} -> {auto 0 prf : x === y} -> {auto 0 req : Extends y z} -> Extends x (MS y z @{req})  
    public export
    data Like : {0 t : Type} -> {m, n : Nat} -> (xs : M m t) -> (ys : M n t) -> Type where 
        [search xs ys]
        LikeZeroL : {0 t : Type} -> {0 m : Nat} -> {a : M m t} -> Like a MZ
        LikeZeroR : {0 t : Type} -> {0 n : Nat} -> {b : M n t} -> Like MZ b
        LikeSucc : 
          {0 t : Type} -> 
          {0 m : Nat} -> {0 n : Nat} -> 
          {0 x : t} -> {0 y : t} -> 
          {0 xs : M m t} -> {0 ys : M n t} -> 
          {auto 0 prf : x === y} -> 
          {auto 0 reqX : Extends x xs} -> {auto 0 reqY : Extends y ys} -> 
          Like (MS x xs @{reqX}) (MS y ys @{reqY})


mutual
    total
    public export 
    castLike : {0 a : Nat} -> (1 xs : M a t) -> ({0 b : Nat} -> {auto 0 p : (a === b)} -> M b t)
    castLike MZ {b = Z} {p = Refl} = MZ
    castLike (MS x xs) {b = S b'} {p = Refl} = MS x (castLike xs {b = b'} {p = Refl}) @{extendsCastLike}
    total 
    private 
    0 extendsCastLike : {n : Nat} -> {x : a} -> {xs : M n a} -> {auto prf : Extends x xs} -> Extends x (castLike xs)
    extendsCastLike {xs=MZ} = %search
    extendsCastLike {prf=prf} {xs=(MS y ys @{prf'})} = ?h3


||| The `Ω` represents a way to obtain an arbitrary number of linear bindings of `t`, so long as they can be projected to
%inline
public export 
0 W : {0 p : Nat -@ Nat} -> (t : Type) -> Type
W {p} t = {1 n : Nat} -> (M (p n) t)
public export
0 W' : (t : Type) -> Type
W' t = W t {p = LId} 
public export  
omega : (t : Type) -> Type
omega t = {0 n : Nat} -> M n t
%name W Ω 
%name omega ω

