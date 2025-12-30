module Data.Grade.Mu


import Data.Grade.Util.Relude
import Decidable.Equality
import Data.Grade.Set
import Data.Linear.LVect
import Prelude.Ops
import Data.Grade.Util.Linear
import Control.Function.FunExt
import Data.Grade.Util.Unique
import Data.Grade.Logic


import Data.Grade.Util.Relude
import Decidable.Equality
import Data.Grade.Set
import Data.Linear.LVect
import Prelude.Ops
import Data.Grade.Util.Linear
import Control.Function.FunExt
import Data.Grade.Util.Unique
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


----------------------------------------------------------------
-- Basic
----------------------------------------------------------------
||| Take a mu of pairs and turn it into a pair of mu's
public export 
push : Mu n (LPair t u) (w0 # w1) -@ (LPair (Mu n t w0) (Mu n u w1))
push MZ = MZ # MZ
push (MS (x # y) z) = let (xs # ys) = push z in (MS x  xs # MS y  ys)
||| Take a pair of mu's and turn it into a mu of pairs
public export 
pull : (LPair (Mu n t w0) (Mu n u w1)) -@ Mu n (LPair t u) (w0 # w1)
pull (MZ # MZ) = MZ
pull (MS x xs # MS y ys) = MS (x # y)  (pull (xs # ys))
  
||| Maps a linear function external to the linear values over a linear mu
public export 
map : (f : t -@ u) -> Mu n t w -@ Mu n u (f w)
map f MZ = MZ
map f (MS x xs) = MS (f x) (map f xs)



private 
applyPair : (LPair (t -@ u) (t)) -@ (u)
applyPair (f # x) = f x

||| Mapping internal to the linear values over a linear mu
public export 
app : Mu n (t -@ u) wf -@ Mu n t wx -@ Mu n u (wf wx)
app MZ MZ = MZ 
app (MS f fs) (MS x xs) = MS (f x) (app fs xs)
----------------------------------------------------------------
-- Operations on Mu
----------------------------------------------------------------
||| Extract the single value from a Mu of size 1
public export
once : Mu 1 t w -@ t
once (MS x MZ) = x

||| Drop a Mu of size 0
public export 
dropMu : {0 n : QNat} -> (0 prf : (n = Zero)) => Mu n t w -@ ()
dropMu MZ = ()
public export
seqMu : {0 n : QNat} -> (0 prf : (n = Zero)) => Mu n t w -@ a -@ a
seqMu MZ x = x

||| Append two Mu's (of the same value) together
public export
combine : Mu m t w -@ Mu n t w -@ Mu (m + n) t w 
combine MZ ys = ys
combine (MS x xs) ys = MS x (combine xs ys)
||| Split a Mu at a given position
public export
split : {1 m : QNat} -> Mu (m + n) t w -@ (Mu m t w) <&> (Mu n t w)
split {m=Zero} xs = And MZ xs
split {m=Succ m'} (MS x xs) = let (And ys zs) = split {m=m'} xs in (And (MS x ys) zs)


||| Join a Mu of Mu's into a single Mu
public export
join : Mu m (Mu n t w) v -@ Mu (m * n) t w
join {m=Zero} MZ = let
  0 prf : (0 * n === 0) = lmul_zero_left
  in rewrite prf in MZ
join {m=Succ m'} (MS x xs) = let
  1 y : Mu n t w = x
  1 ys : Mu (m' * n) t w = join xs
  0 prf : ((Succ m') * n === n + (m' * n)) = lmul_succ_left
  1 z : Mu (Succ m' * n) t w = rewrite prf in combine y ys
  in z


%hint
public export
uniqueMu : {w : t} -> {1 n : QNat} -> Contractible (Mu n t w)
uniqueMu {n=Zero} = contract @{MZ} @{deforming}
  where 
    deforming : {0 y : Mu Zero t w} -> (y === MZ)
    deforming {y=MZ} = Refl

uniqueMu {w} {n=Succ n'} = contract @{MS w uniqueMu.center} @{ ?contract_proof }
    
public export
expand : {1 m : QNat} -> {1 n : QNat} -> Mu (m * n) t w -@ Mu m (Mu n t w) Point 

export
mu_ind :
  {p : (n' : QNat) -> (t : Type) -> (w : t) -> Mu n' t w -> Type} ->
  p 0 t w MZ -@
  ({0 n' : QNat} -> (1 w : t) -> (1 x : Mu n' t w) -> (1 prf : p n' t w x) -> p (Succ n') t w (MS w x)) ->
  {1 n : QNat} ->
  p n t w Point
