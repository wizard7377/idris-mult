module Data.Mult.Ord 

import public Prelude.Types
import Prelude.Ops
import Prelude.Num
import Prelude.Basics
import Data.Linear.LVect
import Data.Linear.LList
import Data.Mult.Classes
import Data.Linear.Notation
import Data.Nat as Data.Nat
import Data.Linear.LNat
import Control.Function
import Prelude.Cast
import Builtin
import PrimIO 

%auto_lazy off
%default total
public export
data Arena : {0 n : Nat} -> (t : Type) -> Type where
  MkArena : AnyPtr -> Arena {n = n} t


||| A number of values 
public export
data M : {0 n : Nat} -> (t : Type) -> Type where
    MS : (1 x : t) -> (1 xs : (Lazy (M {n} t))) -> M {n = S n} t
    MZ : M t {n = Z}
%name M ρ 
public export 
castEq : {0 a : Nat} -> M t {n = a} -@ ({0 b : Nat} -> {auto 0 p : (a === b)} -> M t {n = b})
castEq MZ {b = Z} {p = Refl} = MZ
castEq (MS x xs) {b = S b'} {p = Refl} = MS x (castEq xs {b = b'} {p = Refl})

public export
combine : {t : Type} -> {0 a : Nat} -> {0 b : Nat} -> M t {n = a} -@ M t {n = b} -@ M {n = (a + b)} t
combine MZ y = y
combine (MS x xs) y = MS x (combine xs y)
public export 
W : (t : Type) -> Type
W t = ({1 n : Nat} -> M t {n = n})
%name W ω
export 
{n : Nat} -> LCast (W t) (M t {n = n}) where
  lcast f = f {n = n}
export 
minusEq : {a : Nat} -> (a === (minus a 0))
minusEq {a=Z} = Refl
minusEq {a=(S a')} = Refl
public export
safeMinus : (a : Nat) -> (b : Nat) -> {auto 0 p : LTE b a} -> Nat
safeMinus a b = minus a b
export 
split : {0 a, b : Nat} -> {auto 1 p : LTE b a} -> M t {n = a} -@ (LPair (M t {n = b}) (M {n = (safeMinus a b @{p} )} t))
split {p=LTEZero} xs = (MZ # (castEq @{minusEq} xs))
split {p=LTESucc p'} (MS x xs) = let (ys # zs) = split {p=p'} xs in (MS x ys # zs)


public export
gen : a -> W a
gen x {n} = case n of
  Z => MZ
  (S k) => MS x (Delay (gen x {n = k}))

castToVect : M a {n = n} -@ (LVect n a)
castToVect MZ = Nil
castToVect (MS x xs) = x :: (castToVect (Force xs))

castFromVect : (LVect n a) -@ M a {n = n}
castFromVect Nil = MZ
castFromVect (x :: xs) = MS x (Delay (castFromVect xs))

export 
LCast (M t {n = n}) (LVect n t) where
  lcast = castToVect
export
LCast (LVect n t) (M t {n = n}) where
  lcast = castFromVect
export 
LCast (LVect n t) (Arena {n = n} t) where
  lcast xs = ?h1
export 
LCast (Arena {n = n} t) (LVect n t) where
  lcast (MkArena xs) = ?h2

export 
LCast a (M {n = (S Z)} a) where
  lcast x = MS x (Delay MZ)
export
LCast (M {n = (S Z)} a) a where
  lcast (MS x MZ) = x
export 
Cast a (W a) where
  cast = gen
export 
{n : Nat} -> LCast (W a) (M a {n = n}) where
  lcast f = f {n = n}
export
lowerM' : Consumable t => M {n = (S n)} t -@ M t {n = n}
lowerM' (MS x xs) = let r = seq x xs in r
export
lowerM : Consumable t => {0 a,b : Nat} -> {auto 1 p : LTE b a} -> M t {n = a} -@ M t {n = b}
lowerM {p=LTEZero} MZ = MZ
lowerM {p=LTESucc p'} (MS x xs) = MS x (lowerM {p=p'} (Force xs))
lowerM {p} (MS x xs) = ?h3

safePred : {auto 0 p : IsSucc n} -> Nat -@ Nat
safePred (S k) = k
safePred Z = ?h0
public export
once : {0 n : Nat} -> M {n = (S n)} t -@ (LPair t (M t {n = n}))
once (MS x xs) = (x # (Force xs))

public export
pile : {0 n : Nat} -> t -@ M t {n = n} -@ M {n = (S n)} t
pile x xs = MS x (Delay xs)

public export 
use : {0 n : Nat} -> M {n = (S n)} (a -@ b) -@ a -@ (LPair b (M {n = n}  (a -@ b)))
use fs x = let 
  (r # rs) = once fs
  in (r x # rs)
public export 
use' : M {n = (S Z)} (a -@ b) -@ a -@ b
use' (MS f MZ) x = f x
export 
Consumable (M t {n = Z}) where
  consume MZ = ()

||| This *isn't* like the List version. Each function is used on exactly one element.
apM : {0 n : Nat} -> {0 a, b : Type} -> M {n = n} (a -@ b) -@ M a {n = n} -@ M b {n = n}
apM MZ {n = Z} MZ = MZ
apM {n = (S n')} (MS f fs) (MS x xs) = MS (f x) (apM {n = n'} (Force fs) (Force xs))

export
mapN : {0 n : Nat} -> {0 a, b : Type} -> (a -@ b) -> M a {n = n} -@ M b {n = n}
mapN {n = Z} f MZ = MZ
mapN {n = (S n')} f (MS x xs) = MS (f x) (mapN {n = n'} f xs)
export 
joinN : {t : Type} -> {0 m : Nat} -> {0 n : Nat} -> (M {n = m} (M t {n = n}) -@ M {n = (m * n)} t)
joinN (MS x xs) = combine x (joinN xs)
joinN MZ = MZ

export 
testA : M {n = ?} (Int -@ a) -@ LList a 
testA f = let 
  (r0 # f0) = use f 0  
  (r1 # f1) = use f0 1  
  (r2 # f2) = use f1 2 
  r3 = use' f2 3
  in [r0,r1,r2,r3]

export 
lNat : Nat -@ LNat 
lNat Z = Zero
lNat (S k) = Succ (lNat k)

export 
omega : {1 n : Nat} -> (M {n = n} a -@ b) -@ W a -@ b
omega f g = f (g {n = n})
export 
mapTest : {0 n : Nat} -> M {n = n} (a -@ b) -@ LVect n a -@ LVect n b
mapTest f Nil = seq f Nil
mapTest f (x :: xs) = let 
  (r # fs) = use f x
  in r :: (mapTest fs xs)

public export 
reqType : (f : Type -> Type) -> Type
reqType f = {0 a : Type} -> (0 _ : f a) -> Nat
public export
interface NFunctor (f : Type -> Type) where
  constructor MkNFunctor
  0 req : reqType f
  nmap : 
    {0 a : Type} ->
    {0 b : Type} -> 
    {0 m : Nat} ->
    (1 _ : M {n = m} (a -@ b)) ->
    (1 x : f a) -> 
    {auto 0 prf : (m === req x)} ->
    (f b)


    
0 reqM : {0 n : Nat} -> reqType (M {n = n} )
reqM {n=n} _ = n
export 
implementation {0 n : Nat} -> NFunctor (M {n = n}) where
  req = reqM
  nmap {prf} p x = castEq $ apM p $ castEq @{prf'} x
    where 
        prf' = sym prf
0 reqLVect : {0 n : Nat} -> reqType (LVect n)
reqLVect {n=n} _ = n
export 
implementation {n : Nat} -> NFunctor (LVect n) where
  req = reqLVect
  nmap p x = ?h6
