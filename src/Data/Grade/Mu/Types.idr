module Data.Grade.Mu.Types


import Data.Grade.Util.Relude
import Decidable.Equality
import Data.Grade.Set
import Data.Linear.LVect
import Prelude.Ops
import Data.Grade.Util.Linear
import Control.Function.FunExt
import Data.Grade.Util.Unique
import Data.Grade.Alg
import Data.Grade.CNat
%auto_lazy off
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
data Mu : (n : CNat) -> (t : Type) -> (w : t) -> Type where 
    ||| No more copies available
    MZ : 
        {0 t : Type} ->
        {0 w : t} ->
        Mu 0 t w
    ||| Give one more copy
    ||| @ w The value being copied
    ||| @ xs The remaining copies
    MS : 
        {0 t : Type} -> 
        {0 n : CNat} -> 
        (1 w : t) -> 
        (1 xs : Inf (Mu n t w)) -> 
        Mu (QSucc n) t w
public export
0 witness : Mu n t w -> t
witness _ = w
public export
0 (.witness) : Mu n t w -> t
(.witness) _ = w
 
%inline %tcinline 
public export
mkMu : forall t. (1 x : t) -> Mu 1 t x
mkMu x = (MS x MZ)
%inline %tcinline
public export
unMu : forall t. {0 x : t} -> (1 m : Mu 1 t x) -> t
unMu x = assert_total $ case x of 
    MS y MZ => y
public export
genMu : forall t. (1 src : (!* t)) -> {1 n : CNat} -> (Mu n t {w=unrestricted src})
genMu {t=t} src {n=0} = seq src MZ
genMu {t=t} src {n=n} = ?h5
public export
empty : {auto 0 w : t} -> Mu 0 t w
empty {w} = MZ
public export
0 Repeat : (x : t) -> Mu Fix t x
Repeat x = (MS x (Delay (Repeat x)))
public export 
0 Example : forall t. (n : CNat) -> (w : t) -> Mu n t w
Example 0 w = MZ
Example Fix w = Repeat w
Example n w with (nonZero n)
    Example n w | Yes prf = ?hprf 
    Example n w | No contra = ?hcontra


public export
Consumable (Mu 0 t w) where
    consume x = assert_total $ case x of 
        MZ => ()
  
export 
consumeZero : Consumable (Mu 0 t w) => (0 prf : n === 0) -> (1 m : Mu n t w) -> ()
consumeZero Refl m = consume m

public export
total 
coIndMu : 
    {0 res : {n0 : CNat} -> Inf (Mu n0 t w) -> Type} ->
    (base : ((1 x : Inf (Mu 0 t w)) -> res x)) -> 
    (step : (1 n1 : CNat) -> (1 prev : (1 x : Inf (Mu n1 t w)) -> res x) -> (1 y : (Inf (Mu (QSucc n1)t w))) -> res y) ->
    (1 n : CNat) ->
    (1 m : Inf (Mu n t w)) ->
    res m
coIndMu {res} base step 0 m = base m
coIndMu {res} base step (Fin (Succ n1)) m = assert_total $ let 
    r1 : (
        (1 n2 : QNat) -> 
        (1 n3 : QNat) -> 
        (0 prf : n2 === n3) => 
        ((1 y : Inf (Mu (QSucc (Fin n2)) t w)) -> 
        res y)) 
    r1 n2 n3 @{prf} = (
      step 
        (Fin n2) 
        (rewrite prf in (coIndMu 
          {res=res} 
          base 
          step 
          (Fin n3)
        )))
    1 r0 : ((1 m' : Inf (Mu (Fin (Succ n1)) t w)) -> res m') := copyWithEq r1 n1
    in r0 m
coIndMu {res} base step Fix m = assert_total $ step Fix (coIndMu {res=res} base step Fix) m
    
