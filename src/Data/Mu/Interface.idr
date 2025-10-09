module Data.Mu.Interface 

import Data.Mu.Types
import Data.Mu.Core
import Data.Mu.Lemma
  
import Data.Mu.Util.Relude
import Data.Mu.Util.Nat

%default total
 
public export
interface NFunctor (0 f : (0 t : Type) -> Type) where 
    constructor MkNFunctor
    0 reqF : {0 a : Type} -> (x : f a) -> Nat
    mapN' : {0 a, b : Type} -> (1 x : f a) -> (1 g : ((a -@ b) ^ (reqF x))) -> f b
    
public export
mapN : NFunctor f => {0 n : Nat} -> (1 g : (a -@ b) ^ n) -> (1 x : f a) -> {auto 0 prf : (reqF x) === n} -> f b
mapN g x {prf=prf} = mapN' x (rewrite prf in g)

public export
interface NApplicative (0 f : Type -> Type) where
    constructor MkNApplicative
    pureN' : {0 a : Type} -> (1 x : a) -> f a
    apN' : {0 a, b : Type} -> (1 x : f a) -> (1 y : f b) -> f (LPair a b)

export 
{0 n : Nat} -> NFunctor (Mu n) where
    reqF _ = n
    mapN' (Supply w s) g = ?h0
