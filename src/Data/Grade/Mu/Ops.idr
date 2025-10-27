module Data.Grade.Mu.Ops


import Data.Grade.Util.Relude
import Decidable.Equality
import Data.Grade.Set
import Data.Linear.LVect
import Prelude.Ops
import Data.Grade.Mu.Types
import Data.Grade.Util.Linear
import Control.Function.FunExt
import Data.Grade.Util.Unique

%default total

----------------------------------------------------------------
-- Basic
----------------------------------------------------------------
public export 
push : Mu n (LPair t u) (w0 # w1) -@ (LPair (Mu n t w0) (Mu n u w1))
push MZ = MZ # MZ
push (MS (x # y) z) = let (xs # ys) = push z in (MS x  xs # MS y  ys)
public export 
pull : (LPair (Mu n t w0) (Mu n u w1)) -@ Mu n (LPair t u) (w0 # w1)
pull (MZ # MZ) = MZ
pull (MS x xs # MS y ys) = MS (x # y)  (pull (xs # ys))
public export 
map : (f : t -@ u) -> (1 x : Mu n t w) -> Mu n u (f w)
map f MZ = MZ
map f (MS x xs) = MS (f x) (map {w=x} f xs)

private 
applyPair : (LPair (t -@ u) (t)) -@ (u)
applyPair (f # x) = f x
public export 
app : (1 f : Mu n (t -@ u) wf) -> (1 x : Mu n t wx) -> Mu n u (wf wx)
app MZ MZ = MZ 
app (MS f fs) (MS x xs) = MS (f x) (app fs xs)
  

----------------------------------------------------------------
-- Operations on Mu
----------------------------------------------------------------
public export
once : Mu 1 t w -@ t
once (MS x MZ) = x

public export
0 witness : Mu n t w -> t
witness _ = w

public export 
dropMu : (0 prf : n === 0) => Mu n t w -@ ()
dropMu MZ = ()
public export
seqMu : (0 prf : n === 0) => Mu n t w -@ a -@ a
seqMu MZ x = x
public export
combine : Mu m t w -@ Mu n t w -@ Mu (m + n) t w 
combine MZ ys = ys
combine (MS x xs) ys = MS x (combine xs ys)
public export
split : {1 m : QNat} -> Mu (m + n) t w -@ LPair (Mu m t w) (Mu n t w)
split {m=Zero} xs = MZ # xs
split {m=Succ m'} (MS x xs) = let (ys # zs) = split {m=m'} xs in (MS x ys # zs)
public export
join : Mu m (Mu n t w) v -@ Mu (m * n) t w
join MZ = rewrite lmul_zero_left {k=n} in MZ
join {m=Succ m'} {n=n} (MS x xs) = rewrite prf0 in combine x (the (Mu (m' * n) t w) (join xs))
  where 
    0 prf0 : (lmul (Succ m') n = n + lmul m' n)
    prf0 = rewrite mulRep in Refl
