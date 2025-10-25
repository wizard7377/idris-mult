module Data.Mu.Types 
import Data.Mu.Util.Relude
import public Data.Mu.Util.LPair
import Prelude.Types
import public Data.Mu.Maps
import public Data.Mu.Set
import public Data.Mu.Form
 
%prefix_record_projections off
public export 
data Mu : (n : LNat) -> (t : Type) -> (w : t) -> Type where
    ||| Give one more copy
    ||| @ n Number of copies given (result - 1)
    ||| @ w The value being copied
    ||| @ xs The remaining copies
    MZ : 
        {0 t : Type} ->
        {0 w : t} ->
        Mu Zero t w
    ||| No more copies available
    MS : 
        {0 t : Type} -> 
        {0 n : LNat} -> 
        (1 w : t) -> 
        (1 xs : (Mu n t w)) -> 
        Mu (Succ n) t w
public export
0 witness : Mu n t w -> t
witness _ = w
public export
0 (.witness) : Mu n t w -> t
(.witness) _ = w
 
%inline %tcinline 
public export
mkMu : forall t. (1 x : t) -> Mu LN1 t x
mkMu x = MS x MZ
%inline %tcinline
public export
unMu : forall t. {0 x : t} -> (1 m : Mu LN1 t x) -> t
unMu (MS x MZ) = x
%inline %tcinline
public export
0 A : {ty : Type} -> (p : ty -> Type) -> Type
A {ty} p = LExists {ty=ty} p
public export
0 AM : (n : LNat) -> (t : Type) -> Type
AM n t = A (Mu n t)
export 
infixl 1 ^^
public export
0 (^^) : (t : Type) -> (n : LNat) -> Type
(^^) t n = AM n t

  
public export
0 omega : (t : Type) -> (w : t) -> Type
omega t w = (1 n : LNat) -> (Mu n t w)
public export
0 omegaCps : (t : Type) -> (w : t) -> Type
omegaCps t w = (1 n : LNat) -> (forall r . (Mu n t w -@ r) -@ r)
public export
toCPS : omega t w -@ omegaCps t w
toCPS f n k = k (f {n})
public export
fromCPS : omegaCps t w -@ omega t w
fromCPS f {n} = f n (\x => x)

public export 
0 Omega : (p : Form) -> (t : Type) -> (w : t) -> Type
Omega p t w = (1 n : LNat) -> (Mu (Eval p n) t w)
{-
public export
0 AW : (p : (Qty -@ LNat)) -> (t : Type) -> Type
AW p t = A (Omega p t)
public export
infixl 1 ^
public export
0 (^) :  (t : Type) -> (p : (Qty -@ LNat))-> Type
(^) t p = AW p t
-}
public export
empty : {auto 0 w : t} -> Mu Zero t w
empty {w} = MZ
public export 
0 Example : forall t. (n : LNat) -> (w : t) -> Mu n t w
Example Zero w = MZ
Example (Succ n) w = MS w (Example n w)
public export
0 Repeat : {n : LNat} -> (x : t) -> Mu n t x
Repeat {n=Zero} x = MZ
Repeat {n=Succ n} x = MS x (Repeat {n=n} x)
public export
gen : forall t. (1 src : (!* t)) -> (Omega Id t {w=unrestricted src})
gen {t=t} src {n=Zero} = seq src MZ
gen {t=t} (MkBang src) {n=(Succ n)} = MS src (gen {t=t} (MkBang src) {n=n})
public export 
genMu : forall t. (1 src : (!* t)) -> (1 n : LNat) -> Mu n t (unrestricted src) 
genMu src n = gen src n

public export
Consumable (Mu Zero t w) where
    consume MZ = ()
  
export 
consumeZero : Consumable (Mu Zero t w) => (0 prf : n === Zero) -> (1 m : Mu n t w) -> ()
consumeZero Refl m = consume m
