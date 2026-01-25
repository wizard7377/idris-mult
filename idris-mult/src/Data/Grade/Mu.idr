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
import Prelude.Clone

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
        Mu 0 t w
    ||| Give one more copy
    ||| @ w The value being copied
    ||| @ xs The remaining copies
    MS : 
        {0 t : Type} -> 
        {0 n : QNat} -> 
        (1 w : t) -> 
        (1 xs : (Mu n t w)) -> 
        Mu (Succ n) t w
export 
infix 0 :> 
%inline %tcinline public export
(:>) : (t : Type) -> (w : t) -> QNat -> Type
(:>) t w n = Mu n t w

||| Extract the witness from a mu
||| The arguement itself is ignored, as the witness is in the type
public export
0 witness : Mu n t w -> t
witness _ = w
public export
0 (.witness) : Mu n t w -> t
(.witness) _ = w
%inline %tcinline
public export
unMu : forall t. {0 x : t} -> (1 m : Mu 1 t x) -> t
unMu (MS x MZ) = x

public export
genMu : forall t. (1 src : (!* t)) -> {1 n : QNat} -> (Mu n t {w=unrestricted src})
genMu src {n=Zero} = seq src MZ
genMu (MkBang src) {n=(Succ n)} = MS src (genMu (MkBang src))
  
||| Generate a mu from a unrestricted source 
public export 
gen : forall t. (src : t) -> {1 n : QNat} -> (Mu n t src)
gen src = genMu (MkBang src) 
  
||| The empty mu, of size 0, just given a witness
public export
empty : {auto 0 w : t} -> Mu Zero t w
empty {w} = MZ 
  
||| An example mu, of size n, with all copies being w
public export 
0 Example : forall t. (n : QNat) -> (w : t) -> Mu n t w
Example Zero w = MZ
Example (Succ n) w = MS w (Example n w)
  
||| Repeat a value n times into a Mu, (v ⋄ v ⋄ ... ⋄ v)
public export
0 Repeat : {n : QNat} -> (x : t) -> Mu n t x
Repeat {n=Zero} x = MZ
Repeat {n=Succ n} x = MS x (Repeat {n=n} x)

||| Consume a Mu of size 0
public export
Consumable (Mu Zero t w) where
    consume MZ = ()

||| Drop all values from a Mu
public export 
Drop t => Drop (Mu n t w) where
    drop MZ = ()
    drop (MS x xs) = x >>> drop xs 
export 
consumeZero : Consumable (Mu Zero t w) => (0 prf : n === Zero) -> (1 m : Mu n t w) -> ()
consumeZero Refl m = consume m


----------------------------------------------------------------
-- Basic
----------------------------------------------------------------
||| Take a mu of pairs and turn it into a pair of mu's
public export 
push : Mu n (t :*: u) w -@ ((Mu n t (fst w)) :*: (Mu n u (snd w)))
push MZ = MZ `And` MZ
push (MS (x `And` y) z) = let (xs `And` ys) = push z in (MS x  xs `And` MS y  ys)
||| Take a pair of mu's and turn it into a mu of pairs
public export 
pull : ((Mu n t w0) :*: (Mu n u w1)) -@ Mu n (t :*: u) (And w0 w1)
pull (MZ `And` MZ) = MZ
pull (MS x xs `And` MS y ys) = MS (x `And` y)  (pull (xs `And` ys))
  
||| Maps a linear function external to the linear values over a linear mu
public export 
map : (f : t -@ u) -> Mu n t w -@ Mu n u (f w)
map f MZ = MZ
map f (MS x xs) = MS (f x) (map f xs)

public export 
map' : (f : (1 x : t) -> x === w |- u) -> Mu n t w -@ Mu n u (f w)
map' f MZ = MZ
map' f (MS x xs) = MS (f x) (map' f xs)

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
split : {1 m : QNat} -> {0 n : QNat} -> Mu (m + n) t w -@ (Mu m t w) :*: (Mu n t w)
split {m=Zero} xs = And MZ xs
split {m=Succ m'} (MS x xs) = let (And ys zs) = split {m=m'} xs in (And (MS x ys) zs)


||| Join a Mu of Mu's into a single Mu
public export
join : {0 m , n : QNat} -> {0 v : Mu n t w} -> Mu m (Mu n t w) v -@ Mu (m * n) t w
join {m=Zero} MZ = let
  0 prf : (0 * n === 0) = lmul_zero_left n
  in rewrite prf in MZ
join {m=Succ m'} (MS x xs) = let
  1 y : Mu n t w = x
  1 ys : Mu (m' * n) t w = join xs
  0 prf : ((Succ m') * n === n + (m' * n)) = lmul_succ_left m' n
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
Setpoint : (0 _ : Contractible a) => {0 x, y : a} -> x === y
Setpoint @{ Contract center' prf } {x, y} = let
  0 prfX : x === center' = prf
  0 prfY : center' === y = sym prf
  in trans prfX prfY
export
mu_ind :
  {p : (n' : QNat) -> (t : Type) -> (w : t) -> Mu n' t w -> Type} ->
  p 0 t w MZ -@
  ({0 n' : QNat} -> (1 w : t) -> (1 x : Mu n' t w) -> (1 prf : p n' t w x) -> p (Succ n') t w (MS w x)) ->
  {1 n : QNat} ->
  p n t w Point
public export
extract : Mu 1 t w -@ t
extract (MS w MZ) = w
public export
pure : (1 x : t) -> Mu 1 t x
pure x = MS x MZ
private
0 mu_replace_prim : {n1, n2 : QNat} -> {t1, t2 : Type} -> {w1 : t1} -> {w2 : t} -> (1 prfN : n1 = n2) -> (1 prfT : t1 = t2) -> (1 prfW : w1 ~=~ w2) -> (Mu n1 t1 w1 ~=~ Mu n2 ? w2)
mu_replace_prim {n1} {n2} {t1} {t2} {w1} {w2} prfN prfT prfW = case prfN of
  Refl => case prfT of
    Refl => case prfW of
      Refl => Refl
public export
expand :  {1 m : QNat} -> {1 n : QNat} -> Mu (m * n) t w -@ Mu m (Mu n t w) Point
expand {m=Zero} {n=n} x = dropMu @{ lmul_zero_left n } x `seq` drop {a=QNat} n `seq` MZ
expand {m=Succ m} {n=n} x = let 
    1 [n0, n1] = n.clone 1
    1 [m0, m1] = m.clone 1
    1 x' = expand_off {m=m0.val} {n=n0.val} (rewrite m0.prf in rewrite n0.prf in x)
  in 
    (use_and $ \1 y => \1 ys => let
        1 y' = 
          rewrite n1.prf in rewrite sym n0.prf in y
        1 ys' = 
          rewrite sym m1.prf in 
          rewrite sym n1.prf in 
          rewrite Setpoint {x=y'} in 
          expand {m=assert_smaller m m1.val} {n=assert_smaller n n1.val} $ 
          rewrite CloneEq {a=m1} {b=m0} in 
          rewrite CloneEq {a=n1} {b=n0} in 
          ys
        0 prf : (Mu (Succ m) (Mu n1.val t w) y' = Mu (Succ m) (Mu n t w) Point) = 
          rewrite sym n1.prf in mu_replace_prim %search %search Setpoint
        1 res : Mu (Succ m) (Mu n t w) Point = 
          rewrite sym prf in MS y' ys'
        in m0 >>> res
        ) x'
  where
    1 expand_off : {0 m : QNat} -> {1 n : QNat} -> Mu ((Succ m) * n) t w -@ (Mu n t w) :*: (Mu (m * n) t w)
    expand_off {m, n} v = let 
        1 v' : Mu (n + (m * n)) t w = rewrite sym (lmul_succ_left m n) in v
        in split {m=n} v'
    1 use_and : (a -@ b -@ c) -@ (a :*: b) -@ c
    use_and f (And x y) = f x y

    



public export
react :
  {1 n0, n1 : QNat} -> {0 n2 : QNat} ->
  {0 t, u : Type} -> {0 w_t : t} -> {0 w_u : u} -> {0 w_f : Mu n1 t w_t -@ Mu n2 u w_u} ->
  Mu n0 (Mu n1 t w_t -@ Mu n2 u w_u) w_f -@
  Mu (n0 * n1) t w_t -@
  Mu (n0 * n2) u w_u
react {n0, n1} f x = join $ app f $ expand x

private 
react_sugar : 
  {1 n0, n1 : QNat} -> {0 n2 : QNat} ->  
  forall w_f.
  (((t :> w_t) n1 -@ (u :> w_u) n2) :> w_f) n0 ->
  (t :> w_t) (n0 * n1) -@ (u :> w_u) (n0 * n2)
react_sugar f x = react f x
 
------- MORE LEMMAS
export 
mu_comm : {0 n, m : QNat} -> {0 t : Type} -> {0 w : t} -> Mu (n + m) t w = Mu (m + n) t w
mu_comm {n} {m} = ?mu_comm_proof
  
