module Data.Mu.Lawful.Classes 

import Data.Linear.Notation
import public Data.Linear.Interface 
import Builtin
public export 
interface LFunctor (f : Type -> Type) where
  constructor MkLFunctor
  map1 : {0 a, b : Type} -> (a -@ b) -@ (f a -@ f b)
public export
interface LApplicative (f : Type -> Type) where
  constructor MkLApplicative
  pure1 : {0 a : Type} -> a -@ f a
  ap1 : {0 a, b : Type} -> f (a -@ b) -@ f a -@ f b
public export
interface LMonad (f : Type -> Type) where
    constructor MkLMonad
    join1 : {0 a : Type} -> f (f a) -@ f a


    
ignore : Consumable a => a -@ b -@ b
ignore x y = let z = seq x y in z
export
(<*>) : {f : Type -> Type} -> {0 a, b : Type} -> LApplicative f => f (a -@ b) -@ f a -@ f b
(<*>) = ap1
export
pure : {f : Type -> Type} -> {0 a : Type} -> LApplicative f => a -@ f a
pure = pure1
export
(>>=) : {f : Type -> Type} -> {0 a, b : Type} -> LFunctor f => LMonad f => f a -@ (a -@ f b) -@ f b
(>>=) x f = join1 (map1 f x)

public export
interface LCast (0 a : Type) (0 b : Type) where
    constructor MkLCast
    lcast : a -@ b

export
lcastTo : (0 r : Type) -> {0 a : Type} -> LCast a r => a -@ r
lcastTo r {a} x = lcast x

export 
liftMap : {f : Type -> Type} -> {0 a, b : Type} -> (a -@ b) -@ (a -> b)
liftMap f x = f x

