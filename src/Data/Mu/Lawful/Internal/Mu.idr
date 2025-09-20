module Data.Mu.Lawful.Internal.Mu 

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
import Data.Mu.Types
import Data.Mu.Lawful.Internal.Core
%auto_lazy off
%default total
public export 
react' : {0 m, n, k : Nat} -> M (m + k) (a -@ b) -@ M (n + k) a -@ (LPair (M k b) (LPair (M m (a -@ b)) (M n a)))
react' fs xs = let 
  (f' # fs') = split' @{?h1} {a = m + k} {b = k} fs
  (x' # xs') = split' @{?} {a = n + k} {b = k} xs
  r = apM f' x'
  1 fs'' : M m (a -@ b) = castEq @{?} fs'
  1 xs'' : M n a = castEq @{?} xs'
  in (r # (fs'' # xs''))
export
mapN' : {0 n : Nat} -> {0 a, b : Type} -> (a -@ b) -> M n a -@ M n b
mapN' {n = Z} f MZ = MZ
mapN' {n = (S n')} f (MS x xs) = MS (f x) (mapN' {n = n'} f xs)
export 
joinN' : {t : Type} -> {0 a, b : Nat} -> (M a (M b t) -@ M (a * b) t)
joinN' (MS x xs) = combine' x (joinN' xs)
joinN' MZ = MZ

export 
flatten : {t : Type} -> {0 a, b : Nat} -> (M a (M b t) -@ M (a * b) t)
flatten = joinN'

export 
testA : M ? (Int -@ a) -@ LList a 
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
mapTest : {0 n : Nat} -> M n (a -@ b) -@ LVect n a -@ LVect n b
mapTest f Nil = seq f Nil
mapTest f (x :: xs) = let 
  (r # fs) = use f x
  in r :: (mapTest fs xs)



  
castToVect : M n a -@ (LVect n a)
castToVect MZ = Nil
castToVect (MS x xs) = x :: (castToVect (Force xs))

castFromVect : (LVect n a) -@ M n a
castFromVect Nil = MZ
castFromVect (x :: xs) = MS x (Delay (castFromVect xs))

export 
LCast (M n t) (LVect n t) where
  lcast = castToVect
export
LCast (LVect n t) (M n t) where
  lcast = castFromVect


