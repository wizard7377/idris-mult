module Data.Mu.Simple.Internal.Core

import public Prelude.Types
import Prelude.Ops
import Prelude.Num
import Prelude.Basics
import Data.Linear.LVect
import Data.Mu.Util.Image
import Data.Mu.Util.Nat
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
import Data.Mu.Types
import Data.Mu.Internal.Lemma
%auto_lazy off
%default total
  
{- 
%hint
export 
likeZero : Like x MZ
likeZero = LikeZero
%hint 
export 
likeNext : {auto 0 prf : x === y} -> Like x (MS y ys)
likeNext {prf = Refl} = LikeNext
-}
export 
minusEq : {a : Nat} -> (a === (minus a 0))
minusEq {a=Z} = Refl
minusEq {a=(S a')} = Refl
public export
safeMinus : (a : Nat) -> (b : Nat) -> {auto 0 p : LTE b a} -> Nat
safeMinus a b = minus a b
export 
split' : {0 a, b : Nat} -> {auto 1 p : LTE b a} -> M a t -@ (LPair (M b t) (M (safeMinus a b @{p} ) t))
split' {p=LTEZero} xs = (MZ # (castEq @{minusEq} xs))
split' {p=LTESucc p'} (MS x xs) = let (ys # zs) = split' {p=p'} xs in (MS x ys # zs)


combine : {0 a, b : Nat} -> (xs : Lawful.M a t) -> (ys : Lawful.M b t) -> {auto 0 prf : Like xs ys} -> Lawful.M (a + b) t
combine MZ ys {prf = prf} = castLike ys @{%search}
combine xs MZ {prf = prf} = castLike xs @{?h0}
combine (MS x xs) (MS y ys) {prf} = let 
  prf1 : (x === y) = ?h12312 
  in castLike (MS x (MS y (combine (xs) (ys) @{?h1}) @{?h2}) @{?h3}) @{addSucc2}
export
gen' : a -> W {p=LId} a
gen' x = case n of
  Z => MZ
  (S k) => MS x (Delay (gen' x {n = k}))


||| From a unrestricted modality, obtain a simple `Ω` container
public export
gen : (!* a) -@ W {p=LId} a 
gen (MkBang x) = gen' x
export 
LCast a (M (S Z) a) where
  lcast x = MS x (Delay MZ)
export
LCast (M (S Z) a) a where
  lcast (MS x MZ) = x
export 
Cast a (W {p=LId} a) where
  cast = gen'
export
lowerM' : Consumable t => M (S n) t -@ M n t
lowerM' (MS x xs) = let r = seq x xs in r
 
||| Given that a container `M a t` has at least as many linear bindings as `M b t`, we can convert `M a t` to `M b t`, so long as we can consume any `t`
export
lowerM : Consumable t => {0 a,b : Nat} -> {auto 1 p : LTE b a} -> M a t -@ M b t
lowerM {p=LTEZero} MZ = MZ
lowerM {p=LTESucc p'} (MS x xs) = MS x (lowerM {p=p'} (Force xs))
lowerM {p} (MS x xs) = ?h13
export
safePred : {auto 0 p : IsSucc n} -> Nat -@ Nat
safePred (S k) = k
safePred Z = ?h10
||| The `once` function extracts one linear binding from an `M (S n) t`, returning the element and the remaining `M n t`
public export
once : {0 n : Nat} -> Lawful.M (S n) t -@ (LPair t (Lawful.M n t))
once (MS x xs) = (x # (xs))

once' : {0 n : Nat} -> M (S n) t -@ (LPair t (M n t))
once' (MS x xs) = (x # (Force xs))


public export
pile : {0 n : Nat} -> t -@ M n t -@ M (S n) t
pile x xs = MS x (Delay xs)

public export 
use : {0 n : Nat} -> M (S n) (a -@ b) -@ a -@ (LPair b (M n (a -@ b)))
use fs x = let 
  (r # rs) = once' fs
  in (r x # rs)
public export 
use' : M (S Z) (a -@ b) -@ a -@ b
use' (MS f MZ) x = f x
export 
Consumable (M Z t) where
  consume MZ = ()
export
||| This *isn't* like the List version. Each function is used on exactly one element.
apM : {0 n : Nat} -> {0 a, b : Type} -> M n (a -@ b) -@ M n a -@ M n b
apM MZ {n = Z} MZ = MZ
apM {n=(S n')} (MS f fs) (MS x xs) = MS (f x) (apM {n=n'} (Force fs) (Force xs))

||| The graded push' operation
export 
push' : M n (LPair a b) -@ (LPair (M n a) (M n b))
push' MZ = (MZ # MZ)
push' (MS (x # y) xs) = let (xs' # ys') = push' (Force xs) in (MS x (Delay xs') # MS y (Delay ys'))
||| The graded pull' operation
export
pull' : (LPair (M n a) (M n b)) -@ M n (LPair a b)
pull' (MZ # MZ) = MZ
pull' (MS x xs # MS y ys) = MS (x # y) (Delay (pull' (Force xs # Force ys)))
