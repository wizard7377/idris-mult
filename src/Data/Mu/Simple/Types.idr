module Data.Mu.Simple.Types

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
public export
data M : (0 n : Nat) -> (t : Type) -> Type where
    ||| The inductive case, adds one more linear binding of `t`
    ||| Written in the paper as `x ⊗ xs` 
    MS : {0 n : Nat} -> {0 t : Type} -> (1 x : t) -> (1 xs : (Lazy (M n t))) -> M (S n) t
    ||| The base case, represents zero linear bindings of `t`
    ||| Written in the paper as `⋄`
    MZ : {0 t : Type} -> M Z t

||| A cast that allows you to use a proof that `a` is equal to `b` to convert `M a t` to `M b t`
public export 
castEq : {0 a : Nat} -> M a t -@ ({0 b : Nat} -> {auto 0 p : (a === b)} -> M b t)
castEq MZ {b = Z} {p = Refl} = MZ
castEq (MS x xs) {b = S b} {p = Refl} = MS x (castEq xs {b = b} {p = Refl})


||| The combine operator acts as exponent multiplication, combining two `M` containers into one with the sum of their linear bindings.
||| Written in the paper as `⊙`
public export
combine : {t : Type} -> {0 a, b : Nat} -> M a t -@ M b t -@ M (a + b) t
combine MZ y = y
combine (MS x xs) y = MS x (combine xs y)
  
export 
infixr 7 ++
%inline %tcinline
public export
(++) : {t : Type} -> {0 a, b : Nat} -> M a t -@ M b t -@ M (a + b) t
(++) = combine
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

