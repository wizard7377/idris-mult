module Data.Grade.Mu.Types


import Data.Grade.Util.Relude
import Decidable.Equality
import Data.Grade.Set
import Data.Linear.LVect
import Prelude.Ops
import Data.Grade.Util.Linear
import Control.Function.FunExt
import Data.Grade.Util.Unique
import Data.Grade.CNat
%default total
||| The Core Mu type, the core construction of this system 
||| Intuitively, `Mu n t w` represents `n` copies of the value `w` of type `t`
||| Ie, it is the equivalent of the *judgement* `x : w [n]` as an Idris type
||| 
||| This is very much like the `Copies` datatype, per as a matter of fact if `t` were implicit (and we used `Nat` instead of `QNat`) they would be the same type
||| The choice for both of these had to do with their intended use 
|||
||| @ n The number of copies available
||| @ t The underlying type
||| @ w The witness for the type
public export 
data Mu : (n : QNat) -> (t : Type) -> (w : t) -> Type where 
    ||| No more copies available
    MZ : 
        {0 t : Type} ->
        {0 w : t} ->
        Mu Zero t w
    ||| Give one more copy
    ||| @ w The value being copied
    ||| @ xs The remaining copies
    MS : 
        {0 t : Type} -> 
        {0 n : QNat} -> 
        (1 w : t) -> 
        (1 xs : (Mu n t w)) -> 
        Mu (Succ n) t w

||| The Core Mu type, the core construction of this system 
||| Intuitively, `Mu n t w` represents `n` copies of the value `w` of type `t`
||| Ie, it is the equivalent of the *judgement* `x : w [n]` as an Idris type
||| 
||| This is very much like the `Copies` datatype, per as a matter of fact if `t` were implicit (and we used `Nat` instead of `QNat`) they would be the same type
||| The choice for both of these had to do with their intended use 
|||
||| @ n The number of copies available
||| @ t The underlying type
||| @ w The witness for the type
public export 
data CMu : (n : CNat) -> (t : Type) -> (w : t) -> Type where 
    ||| No more copies available
    CMZ : 
        {0 t : Type} ->
        {0 w : t} ->
        CMu 0 t w
    ||| Give one more copy
    ||| @ w The value being copied
    ||| @ xs The remaining copies
    CMS : 
        {0 t : Type} -> 
        {0 n : CNat} -> 
        (1 w : t) -> 
        (1 xs : Inf (CMu n t w)) -> 
        CMu (QSucc n) t w
  
public export
view : {1 n : QNat} -> CMu (Fin n) t w -> Mu n t w
view {n=Zero} CMZ = MZ
view _ = ?view_rhs
  
public export
review : {1 n : QNat} -> Mu n t w -> CMu (Fin n) t w
review {n=Zero} MZ = CMZ
review {n=Succ n} (MS x xs) = rewrite finQSucc {n=n} in CMS x (review {n=n} xs)
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

public export
genMu : forall t. (1 src : (!* t)) -> {1 n : QNat} -> (Mu n t {w=unrestricted src})
genMu {t=t} src {n=Zero} = seq src MZ
genMu {t=t} (MkBang src) {n=(Succ n)} = MS src (genMu {t=t} (MkBang src) {n=n})
public export
empty : {auto 0 w : t} -> Mu Zero t w
empty {w} = MZ
public export 
0 Example : forall t. (n : QNat) -> (w : t) -> Mu n t w
Example Zero w = MZ
Example (Succ n) w = MS w (Example n w)
public export
0 Repeat : {n : QNat} -> (x : t) -> Mu n t x
Repeat {n=Zero} x = MZ
Repeat {n=Succ n} x = MS x (Repeat {n=n} x)

public export
Consumable (Mu Zero t w) where
    consume MZ = ()
  
export 
consumeZero : Consumable (Mu Zero t w) => (0 prf : n === Zero) -> (1 m : Mu n t w) -> ()
consumeZero Refl m = consume m
