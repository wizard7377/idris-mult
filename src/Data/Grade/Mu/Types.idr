module Data.Grade.Mu.Types


import Data.Grade.Util.Relude
import Decidable.Equality
import Data.Grade.Set
import Data.Linear.LVect
import Prelude.Ops
import Data.Grade.Util.Linear
import Control.Function.FunExt
import Data.Grade.Util.Unique

%default total

public export 
data Mu : (n : QNat) -> (t : Type) -> (w : t) -> Type where
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
        {0 n : QNat} -> 
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
