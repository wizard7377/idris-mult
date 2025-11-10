module Data.Grade.Alg.Types
import Data.Linear.Notation
import Prelude
import Decidable.Equality
public export
falso : forall t. (0 contra : Void) -> t
falso contra impossible

export
infix 6 =?

public export
JOr : Type -> Type -> Type
JOr = Either
public export
interface Alg a where
    %inline
    0 (=?) : (x : a) -> (y : a) -> Type 
    (=?) = (===)
    0 aeq : (x : a) -> (y : a) -> Dec (x =? y)
    toAlg : Integer -> a
    %inline
    0 ALTE : a -> a -> Type 
    1 aadd : a -@ a -@ a
    1 amul : a -@ a -@ a
public export
interface Alg a => Count a where 
  0 NonZero : a -> Type
  0 nonZero : (x : a) -> Dec (NonZero x)
  1 ASucc : (1 x : a) -> a
  1 APred : (1 x : a) -> (0 prf : NonZero x) => a
  
public export
interface Alg a => Trail a where
    1 amax : a -@ a -@ a 
    1 amin : a -@ a -@ a 
    
public export 
interface Trail a => Alg a => Count a => Lawful a where 
    1 LZero : a 
    LZero = toAlg 0
    1 LOne : a
    LOne = toAlg 1
    0 addZero : {x : a} -> aadd x LZero =? x
    addZero = believe_me ()
    0 addSucc : {x, y : a} -> aadd x (ASucc y) =? ASucc (aadd x y)
    addSucc = believe_me ()
    0 nonZeroSucc : {x : a} -> NonZero (ASucc x)
    nonZeroSucc = believe_me ()
    0 predSucc : {x : a} -> (prf : NonZero (ASucc x)) => APred (ASucc x) =? x
    predSucc = believe_me ()
    0 succPred : {x : a} -> (prf : NonZero x) => ASucc (APred x) =? x
    succPred = believe_me ()
    0 mulZero : {x : a} -> amul x LZero =? LZero
    mulZero = believe_me ()
    0 mulOne : {x : a} -> amul x LOne =? x
    mulOne = believe_me ()
    0 mulSucc : {x, y : a} -> amul x (ASucc y) =? aadd x (amul x y)
    mulSucc = believe_me ()
    0 zeroSuccNot : {x : a} -> Not (LZero =? ASucc x)
    zeroSuccNot = believe_me ()
    0 succInj : {x, y : a} -> (ASucc x =? ASucc y) -> (x =? y)
    succInj prf = believe_me ()
    0 succNeq : {y : a} -> ({x : a} -> Not (ASucc x =? y)) => (LZero =? y)
    succNeq = believe_me ()
public export
Alg a => Num a where 
    (+) x y = aadd x y
    (*) x y = amul x y
    fromInteger x = toAlg (cast x)

