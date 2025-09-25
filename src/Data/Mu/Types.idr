module Data.Mu.Types 
import Data.Mu.Util.Relude
import public Data.DPair
public export 
data M : (n : Nat) -> (t : Type) -> {w : t} -> Type where
    ||| Give one more copy
    ||| @ n Number of copies given (result - 1)
    ||| @ w The value being copied
    ||| @ xs The remaining copies
    MZ : 
        {0 t : Type} ->
        {0 w : t} ->
        M Z t {w}
    ||| No more copies available
    MS : 
        {0 t : Type} -> 
        {0 n : Nat} -> 
        {0 w : t} ->
        (1 w : t) -> 
        (1 xs : Lazy (M n t {w})) -> 
        M (S n) t {w}
public export
%inline %tcinline
0 M' : (n : Nat) -> (t : Type) -> (w : t) -> Type
M' n t w = M n t {w} 
%inline %tcinline
public export
Proj : Type 
Proj = Nat -@ Nat

public export
IdProj : Proj
IdProj n = n
  
public export
record LExists (f : ty -> Type) where
    constructor LEvidence
    0 fst : ty 
    1 snd : f fst
export 
infixl 1 ^
public export
0 (^) : (t : Type) -> (n : Nat) -> Type
(^) t n = LExists (M' n t)

||| The Ω type, which can produce any number of `t` that are projected to by `p`
||| Useful, as this allows there to be functor from the type of ℒ of `M` to ℒ of `Ω`
public export 
0 W : (p : Proj) -> (t : Type) -> {w : t} -> Type
W p t {w} = (n : Nat) -> (M (p n) t {w})
%inline %tcinline
public export 
0 W' : (p : Proj) -> (t : Type) -> (w : t) -> Type
W' p t w = W p t {w}


||| The ω type, which can produce any number of `t`
%inline %tcinline
public export 
0 Omega : (t : Type) -> Type
Omega t = LExists (W' id t)
export 
infixl 1 ^-
public export
0 (^-) : (0 t : Type) -> (0 p : Proj) -> Type
(^-) t p = LExists (W' p t)
  
  


%inline %tcinline
public export
0 MapTo : (p : Proj) -> (n : Nat) -> Type
MapTo p n = (m : Nat ** ((p m) === n))

