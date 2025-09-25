module Data.Mu.Types 
import Data.Mu.Util.Relude
import public Data.DPair
  
%prefix_record_projections off
public export 
data M : (n : Nat) -> (t : Type) -> (w : t) -> Type where
    ||| Give one more copy
    ||| @ n Number of copies given (result - 1)
    ||| @ w The value being copied
    ||| @ xs The remaining copies
    MZ : 
        {0 t : Type} ->
        {0 w : t} ->
        M Z t w
    ||| No more copies available
    MS : 
        {0 t : Type} -> 
        {0 n : Nat} -> 
        {0 w : t} ->
        (1 w : t) -> 
        (1 xs : (M n t w)) -> 
        M (S n) t w
%inline %tcinline
public export
Proj : Type 
Proj = Nat -@ Nat

public export
IdProj : Proj
IdProj n = n
  
%prefix_record_projections off
public export
record LExists (f : ty -> Type) where
    constructor LEvidence
    0 fst' : ty 
    1 snd' : f fst'

public export
%inline %tcinline
0 (.fst) : {0 ty : Type} -> {0 f : ty -> Type} -> LExists f -> ty
(.fst) (LEvidence x y) = x
public export
%inline %tcinline
(.snd) : {0 ty : Type} -> {0 f : ty -> Type} -> (1 e : LExists f) -> f (e .fst)
(.snd) (LEvidence x y) = y

public export
%inline %tcinline
0 fst : {0 ty : Type} -> {0 f : ty -> Type} -> LExists f -> ty
fst (LEvidence x y) = x
public export
%inline %tcinline
snd : {0 ty : Type} -> {0 f : ty -> Type} -> (1 e : LExists f) -> f (e .fst)
snd (LEvidence x y) = y

public export
%inline %tcinline
0 fstL : {0 ty : Type} -> {0 f : ty -> Type} -> LExists f -> ty
fstL (LEvidence x y) = x
public export
%inline %tcinline
sndL : {0 ty : Type} -> {0 f : ty -> Type} -> (1 e : LExists f) -> f (e .fst)
sndL (LEvidence x y) = y


export 
infixl 1 ^
public export
0 (^) : (t : Type) -> (n : Nat) -> Type
(^) t n = LExists (M n t)

||| The Ω type, which can produce any number of `t` that are projected to by `p`
||| Useful, as this allows there to be functor from the type of ℒ of `M` to ℒ of `Ω`
public export 
0 W : (p : Proj) -> (t : Type) -> (w : t) -> Type
W p t w = (n : Nat) -> (M (p n) t w)
export 
infixl 1 ^^
public export
0 (^^) : (t : Type) -> (p : Proj) -> Type
(^^) t p = LExists (W p t)


  


%inline %tcinline
public export
0 MapTo : (p : Proj) -> (n : Nat) -> Type
MapTo p n = (m : Nat ** ((p m) === n))

