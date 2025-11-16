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
import Data.Grade.CNat
%default total

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
map' : (f : t -@ u) -> (1 x : Mu n t w) -> Mu n u (f w)
map' f MZ = MZ
map' f (MS x xs) = MS (f x) (map' {w=x} f xs)

||| Co-mu equivalent of push
covering public export
cpush : CMu n (LPair t u) (w0 # w1) -@ (LPair ((CMu n t w0)) ((CMu n u w1)))
cpush CMZ = CMZ # CMZ
cpush (CMS (x # y) z) = let (xs # ys) = cpush z in (CMS x xs # CMS y ys)
||| Co-mu equivalent of pull
covering public export
cpull : {1 n : CNat} -> (LPair (CMu n t w0) (CMu n u w1)) -@ CMu n (LPair t u) (w0 # w1)
cpull (CMZ # CMZ) = CMZ
cpull {n=n} z = ?zz2
||| Co-mu equivalent of map'
public export 
cmap' : (f : t -@ u) -> (1 x : CMu n t w) -> CMu n u (f w)
cmap' f CMZ = CMZ
cmap' f (CMS x xs) = CMS (f x) (cmap' f xs)


private 
applyPair : (LPair (t -@ u) (t)) -@ (u)
applyPair (f # x) = f x

||| Mapping internal to the linear values over a linear mu
public export 
app : (1 f : Mu n (t -@ u) wf) -> (1 x : Mu n t wx) -> Mu n u (wf wx)
app MZ MZ = MZ 
app (MS f fs) (MS x xs) = MS (f x) (app fs xs)

public export
capp : {0 n : CNat} -> (1 f : CMu n (t -@ u) wf) -> (1 x : CMu n t wx) -> CMu n u (wf wx) 
capp CMZ CMZ = CMZ
capp f x = ?zz3

----------------------------------------------------------------
-- Operations on Mu
----------------------------------------------------------------
||| Extract the single value from a Mu of size 1
public export
once : Mu 1 t w -@ t
once (MS x MZ) = x
||| Extract the single value from a co-Mu of size 1
public export
conce : CMu 1 t w -@ t
conce x = case x of 
  CMS y CMZ => y
  _ => ?zz1
||| Get the witness value from a Mu
||| This never actually uses the arguement, just the type
public export
0 witness : Mu n t w -> t
witness _ = w
||| Drop a Mu of size 0
public export 
dropMu : (0 prf : n === 0) => Mu n t w -@ ()
dropMu MZ = ()
public export
seqMu : (0 prf : n === 0) => Mu n t w -@ a -@ a
seqMu MZ x = x

||| Append two Mu's (of the same value) together
public export
combine : Mu m t w -@ Mu n t w -@ Mu (m + n) t w 
combine MZ ys = ys
combine (MS x xs) ys = MS x (combine xs ys)
||| Split a Mu at a given position
public export
split : {1 m : QNat} -> Mu (m + n) t w -@ LPair (Mu m t w) (Mu n t w)
split {m=Zero} xs = MZ # xs
split {m=Succ m'} (MS x xs) = let (ys # zs) = split {m=m'} xs in (MS x ys # zs)
||| Join a Mu of Mu's into a single Mu
public export
join : Mu m (Mu n t w) v -@ Mu (m * n) t w
join MZ = rewrite lmul_zero_left {k=n} in MZ
join {m=Succ m'} {n=n} (MS x xs) = rewrite prf0 in combine x (the (Mu (m' * n) t w) (join xs))
  where 
    0 prf0 : (lmul (Succ m') n = n + lmul m' n)
    prf0 = rewrite mulRep in Refl
