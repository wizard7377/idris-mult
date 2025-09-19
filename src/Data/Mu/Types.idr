module Data.Mu.Types

import public Prelude.Types
import Prelude.Ops
import Prelude.Num
import Prelude.Basics
import Data.Linear.LVect
import Data.Mu.Util.Image
import Data.Linear.LList
import Data.Mu.Classes
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
    data M' : (0 n : Nat) -> (t : Type) -> Type where
        ||| The inductive case, adds one more linear binding of `t`
        ||| Written in the paper as `x ⊗ xs` 
        MS' : (1 x : t) -> (1 xs : (M' n t)) -> {auto 0 prf : Extends x xs} -> M' (S n) t
        ||| The base case, represents zero linear bindings of `t`
        ||| Written in the paper as `⋄`
        MZ' : M' Z t

    public export 
    data Extends : {0 a : Type} -> {n : Nat} -> (x : a) -> (xs : M' n a) -> Type where 
        ExtendsZero : Extends x MZ'
        ExtendsSucc : {auto 0 prf : x === y} -> {auto 0 prf' : Extends y ys} -> Extends x (MS' y ys @{prf'})  
    public export
    data Like : {0 t : Type} -> {n : Nat} -> (xs : M' n t) -> (ys : M' n t) -> Type where 
        LikeZeroL : Like _ MZ'
        LikeZeroR : Like MZ' _
        LikeNext : {auto 0 prf : x === y} -> {auto 0 prfX : Extends x xs} -> {auto 0 prfY : Extends y ys} -> Like (MS' x xs @{prfX}) (MS' y ys @{prfY})
public export
data M : (0 n : Nat) -> (t : Type) -> Type where
    ||| The inductive case, adds one more linear binding of `t`
    ||| Written in the paper as `x ⊗ xs` 
    MS : (1 x : t) -> (1 xs : (Lazy (M n t))) -> M (S n) t
    ||| The base case, represents zero linear bindings of `t`
    ||| Written in the paper as `⋄`
    MZ : M Z t

%unsafe
export
unsafeBoxM : M n t -@ M' n t
unsafeBoxM MZ = MZ'
unsafeBoxM (MS x xs) = MS' x (unsafeBoxM (Force xs)) @{believe_me ()}
export 
safeUnboxM : M' n t -@ M n t 
safeUnboxM MZ' = MZ
safeUnboxM (MS' x xs) = MS x (Delay (safeUnboxM xs))
||| A cast that allows you to use a proof that `a` is equal to `b` to convert `M a t` to `M b t`
public export 
castEq : {0 a : Nat} -> M a t -@ ({0 b : Nat} -> {auto 0 p : (a === b)} -> M b t)
castEq MZ {b = Z} {p = Refl} = MZ
castEq (MS x xs) {b = S b'} {p = Refl} = MS x (castEq xs {b = b'} {p = Refl})

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

