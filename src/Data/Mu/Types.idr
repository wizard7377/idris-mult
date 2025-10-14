module Data.Mu.Types 
import Data.Mu.Util.Relude
import public Data.Mu.Util.LPair

%inline %tcinline
public export
0 Proj : {ty : Type} -> Type 
Proj {ty} = (1 x : Nat) -> ty
%inline %tcinline
public export
0 Pred : {ty : Type} -> Type 
Pred {ty} = (1 x : ty) -> Type

public export
0 MapsTo : (p : Proj {ty=ty}) -> ty -> Type
MapsTo p y = LExists {ty=Nat} (\x => p x === y)
public export
IdProj : Proj {ty=Nat}
IdProj n = n

 
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
        (1 w : t) -> 
        (1 xs : (Mu n t w)) -> 
        Mu (S n) t w
public export
0 witness : Mu n t w -> t
witness _ = w
public export
0 (.witness) : Mu n t w -> t
(.witness) _ = w
%inline %tcinline
public export
0 A : {ty : Type} -> (p : ty -> Type) -> Type
A {ty} p = LExists {ty=ty} p
public export
0 AM : (n : Nat) -> (t : Type) -> Type
AM n t = A (Mu n t)
export 
infixl 1 ^^
public export
0 (^^) : (t : Type) -> (n : Nat) -> Type
(^^) t n = AM n t

  
public export
0 omega : (t : Type) -> (w : t) -> Type
omega t w = (1 n : Nat) -> (Mu n t w)
public export
0 omegaCps : (t : Type) -> (w : t) -> Type
omegaCps t w = (1 n : Nat) -> (forall r . (Mu n t w -@ r) -@ r)
public export
toCPS : omega t w -@ omegaCps t w
toCPS f n k = k (f {n})
public export
fromCPS : omegaCps t w -@ omega t w
fromCPS f n = f n (\x => x)
namespace Proj
    public export
    0 Omega : (p : Proj {ty=Nat}) -> (t : Type) -> (w : t) -> Type
    Omega p t w = (1 n : Nat) -> (Mu (p n) t w)
namespace Pred
    public export 
    0 Omega : (p : Pred {ty=Nat}) -> (t : Type) -> (w : t) -> Type
    Omega p t w = (1 n : Nat) -> {auto 0 prf : p n} -> (Mu n t w)
{-
public export
0 AW : (p : (Nat -@ Nat)) -> (t : Type) -> Type
AW p t = A (Omega p t)
public export
infixl 1 ^
public export
0 (^) :  (t : Type) -> (p : (Nat -@ Nat))-> Type
(^) t p = AW p t
-}
public export
empty : {auto 0 w : t} -> Mu Z t w
empty {w} = MZ
public export 
0 example : forall t. (n : Nat) -> (w : t) -> Mu n t w
example Z w = MZ
example (S n) w = MS w (example n w)
%inline %tcinline
public export
0 MapTo : (p : Proj {ty=Nat}) -> (n : Nat) -> Type
MapTo p n = (m : Nat ** ((p m) === n))
public export
Consumable Nat where
    consume Z = ()
    consume (S n) = consume n 
public export
Duplicable Nat where
    duplicate Z = (Z :: Z :: Nil)
    duplicate (S n) = let (n :: n :: Nil) = duplicate n in (S n :: S n :: Nil)
public export
Comonoid Nat where
    counit Z = ()
    counit (S n) = counit n 
    comult Z = (Z # Z)
    comult (S n) = let (m0 # m1) = comult n in (S m0 # S m1)
