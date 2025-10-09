module Data.Mu.Types 
import Data.Mu.Util.Relude
import public Data.Mu.Util.LPair
  
%prefix_record_projections off
public export 
data Mu : (n : Nat) -> (t : Type) -> (w : t) -> Type where
    ||| Give one more copy
    ||| @ n Number of copies given (result - 1)
    ||| @ w The value being copied
    ||| @ xs The remaining copies
    MZ : 
        {0 t : Type} ->
        {0 w : t} ->
        Mu Z t w
    ||| No more copies available
    MS : 
        {0 t : Type} -> 
        {0 n : Nat} -> 
        {0 w : t} ->
        (1 w : t) -> 
        (1 xs : (Mu n t w)) -> 
        Mu (S n) t w

%inline %tcinline
public export
0 A : {ty : Type} -> (p : ty -> Type) -> Type
A {ty} p = LExists {ty=ty} p
public export
0 AM : (n : Nat) -> (t : Type) -> Type
AM n t = A (Mu n t)
export 
infixl 1 ^
public export
0 (^) : (t : Type) -> (n : Nat) -> Type
(^) t n = AM n t


%inline %tcinline
public export
Proj : Type 
Proj = Nat -@ Nat

public export
IdProj : Proj
IdProj n = n
  
%inline %tcinline
public export
0 omega : (t : Type) -> (w : t) -> Type
omega t w = (n : Nat) -> (Mu n t w)
||| The Ω type, which can produce any number of `t` that are projected to by `p`
||| Useful, as this allows there to be functor from the type of ℒ of `Mu` to ℒ of `Ω`
public export 
0 Omega : (p : (Nat -@ Nat)) -> (t : Type) -> (w : t) -> Type
Omega p t w = (n : Nat) -> (Mu (p n) t w) 
public export
0 AW : (p : (Nat -@ Nat)) -> (t : Type) -> Type
AW p t = A (Omega p t)
public export
infixl 1 ^^
public export
0 (^^) :  (t : Type) -> (p : (Nat -@ Nat))-> Type
(^^) t p = AW p t



%inline %tcinline
public export
0 MapTo : (p : Proj) -> (n : Nat) -> Type
MapTo p n = (m : Nat ** ((p m) === n))

