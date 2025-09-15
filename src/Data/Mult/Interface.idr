module Data.Mult.Interface 

import Data.Mult.Types
import Data.Linear.LVect
import Data.Linear.Notation
import Prelude.Ops
import Data.Nat 
import Prelude.Num
import Prelude.Basics
import Builtin

%hide Data.Linear.LVect.(<$>)
public export 
reqType : (f : Type -> Type) -> Type
reqType f = {0 a : Type} -> (0 _ : f a) -> Nat

public export
reqType2 : (f : Type -> Type) -> Type
reqType2 f = {0 a, b : Type} -> (0 _ : f a) -> (0 _ : f b) -> Nat
public export
interface NFunctor (0 f : Type -> Type) where
  constructor MkNFunctor
  0 reqF : reqType f
  nmap : 
    {0 a, b : Type} ->
    {0 m : Nat} ->
    (1 _ : M m (a -@ b)) ->
    (1 x : f a) -> 
    {auto 0 prf : (m === reqF x)} ->
    (f b)
  nmap' : 
    {0 a, b : Type} ->
    (1 x : f a) -> 
    (1 _ : M (reqF x) (a -@ b)) ->
    (f b)
  nmap {a, b} x {prf} f = nmap' f $ castEq x
  nmap' {a, b} f x = nmap x f
    
public export 
interface NApplicative (0 f : Type -> Type) where 
    constructor MkNApplicative
  reqA : Nat
  pureN : M reqA a -@ f a
  apN : f (a -@ b) -@ f a -@ f b

public export
interface NMonad (0 f : Type -> Type) where
  constructor MkNMonad
  reqN : reqType f
  joinN : (1 x : f (f a)) -> M (reqN x) (f a)
  
0 reqM : {0 n : Nat} -> reqType (M n )
reqM {n} _ = n
export 
implementation {0 n : Nat} -> NFunctor (M n) where
  reqF = reqM
  nmap {prf} p x = castEq $ apM p $ castEq @{prf'} x
    where 
        prf' = sym prf
 
export 
implementation {n : Nat} -> NApplicative (M n) where
  reqA = n
  pureN = id
  apN f x = apM f x
export
implementation {n : Nat} -> NMonad (M n) where
    reqN {} _ = n
    joinN = id
  
0 reqLVect : {0 n : Nat} -> reqType (LVect n)
reqLVect {n} _ = n
export 
implementation {n : Nat} -> NFunctor (LVect n) where
  reqF = reqLVect
  nmap p x = ?h7
(<$>) : 
        {f : Type -> Type} ->
        NFunctor f =>
        {0 a, b : Type} ->
        {0 m : Nat} ->
        (1 _ : M m (a -@ b)) ->
        (1 x : f a) -> 
        {auto 0 prf : (m === reqF x)} ->
        (f b)
f <$> x = nmap f x

--pure : NApplicative f => M reqA a -@ f a
--pure = ?h5
(<*>) : NApplicative f => f (a -@ b) -@ f a -@ f b
(<*>) = apN
  
