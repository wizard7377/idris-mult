module Data.Mu.Lawful.Interface 

import Data.Mu.Lawful.Types
import Data.Linear.LVect
import Data.Linear.Notation
import Data.Linear.LMaybe
import Data.Linear.Interface
import Prelude.Ops
import Data.Nat 
import Prelude.Num
import Prelude.Basics
import Builtin

%hide Data.Linear.LVect.(<$>)
public export 
0 reqType : (f : Type -> Type) -> Type
reqType f = {a : Type} -> (x : f a) -> Nat

public export
reqType2 : (f : Type -> Type) -> Type
reqType2 f = {0 a, b : Type} -> (0 _ : f a) -> (0 _ : f b) -> Nat
public export
interface NFunctor (0 f : Type -> Type) where
  constructor MkNFunctor
  0 req : reqType f
  mapN' : 
    {0 a, b : Type} ->
    {0 m : Nat} ->
    (1 _ : Lawful.M m (a -@ b)) ->
    (1 x : f a) -> 
    {auto 0 prf : (m === req x)} ->
    (f b)
  mapN'' : 
    {0 a, b : Type} ->
    (1 x : f a) -> 
    (1 _ : Lawful.M (req x) (a -@ b)) ->
    (f b)
  mapN' {a, b} x {prf} f = mapN'' f $ castEq x
   
public export 
interface NApplicative (0 f : Type -> Type) where
  constructor MkNApplicative
  pureN : {0 a : Type} -> a -@ f a
  appN : (f (a -@ b)) -@ f a -@ f b
 
public export
interface NMonad (0 f : Type -> Type) where
    constructor MkNMonad
    0 flat : {0 a : Type} -> f (f a) -@ Nat
    joinN' : {0 a : Type} -> (1 x : f (f a)) -> (Lawful.M (flat x) (f a))
(<$>) : 
        {f : Type -> Type} ->
        NFunctor f =>
        {0 a, b : Type} ->
        {0 m : Nat} ->
        (1 _ : Lawful.M m (a -@ b)) ->
        (1 x : f a) -> 
        {auto 0 prf : (m === req x)} ->
        (f b)
f <$> x = mapN' f x
export
pure : {f : Type -> Type} -> NApplicative f => {0 a : Type} -> a -@ f a
pure = pureN 
export
(<*>) : {f : Type -> Type} -> {0 a, b : Type} -> NApplicative f => f (a -@ b) -@ f a -@ f b
(<*>) = appN
export 
(>>=) : {m : Type -> Type} -> {0 a, b : Type} -> NFunctor m => NMonad m => (1 x : m a) -> (1 f : Lawful.M (req x) (a -@ m b)) -> Lawful.M ? (m b)
(>>=) x f = joinN' (mapN' f x)


Duplet : Type -> Type 
Duplet x = LPair x x
reqPair : reqType Duplet
reqPair x = 2

NFunctor Duplet where
  req = reqPair
  mapN'' {a, b} (x # y) f = let 
                                (r1 # f1) = use f x
                                (r2 # f2) = use f1 y
                            in seq f2 (r1 # r2)

  
reqMaybe : reqType LMaybe
reqMaybe Nothing = 0 
reqMaybe (Just _) = 1
NFunctor LMaybe where
  req x = reqMaybe x
  mapN'' {a, b} Nothing f = seq f Nothing
  mapN'' {a, b} (Just x) f = let (r # f') = use f x in seq f' $ Just r
