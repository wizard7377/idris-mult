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
%auto_lazy off
----------------------------------------------------------------
-- Basic
----------------------------------------------------------------
public export 
push : {0 n : CNat} -> Mu n (LPair t u) (w0 # w1) -@ (LPair (Mu n t w0) (Mu n u w1))
push MZ = MZ # MZ
push (MS (x # y) z) = assert_total $ let (xs # ys) = push z in (MS x xs # MS y ys)
public export 
pull : {0 n : CNat} -> (LPair (Mu n t w0) (Mu n u w1)) -@ Mu n (LPair t u) (w0 # w1)
pull {n=0} (x # MZ) = seq x MZ
pull {n=0} (MZ # y) = seq y MZ
pull {n=QSucc n} (MS {n=n} x xs # MS y ys) = MS (x # y) (pull (xs # ys))
public export 
map : (f : t -@ u) -> (1 x : Mu n t w) -> Mu n u (f w)
map f MZ = MZ
map f (MS x xs) = MS (f x) (map {w=x} f xs)

private 
applyPair : (LPair (t -@ u) (t)) -@ (u)
applyPair (f # x) = f x
public export 
app : {0 n : CNat} -> (1 f : Mu n (t -@ u) wf) -> (1 x : Mu n t wx) -> Mu n u (wf wx)
app f x = let 1 fx = pull (f # x) in map applyPair fx 

----------------------------------------------------------------
-- Operations on Mu
----------------------------------------------------------------

||| TODO: Make this actually work
public export
once : Mu (Fin 1) t w -@ t
once x = assert_total $ case x of 
    MS y MZ => y
public export
0 witness : Mu n t w -> t
witness _ = w

public export 
dropMu : {0 n : CNat} -> (0 prf : n === 0) => Mu n t w -@ ()
dropMu {n=0} MZ = ()
dropMu {n=QSucc n'} (MS {n=n'} x xs) = ?hdm
public export
seqMu : (0 prf : n === 0) => Mu n t w -@ a -@ a
seqMu m x = let () = dropMu @{prf} m in x
public export
combine : Mu m t w -@ Mu n t w -@ Mu (cadd m n) t w 
public export
split : Finite m => Mu (cadd (m) n) t w -@ LPair (Mu (m) t w) (Mu n t w)

-- split {m=0, n=n} xs = MZ # ?h0
{-
split {m=Succ m'} x = let 
  1 x' : (Mu (QSucc (cadd (Fin m') n)) t w) = (rewrite sym prf0 in x) -- let (ys # zs) = split {m=m'} xs in (MS x ys # zs)
  1 (MS {n = ?h5} y ys) = x'
  1 (z0 # z1) : LPair (Mu (Fin m') t w) (Mu n t w) = ?h2 -- split {m=m', n=n} ys
  in ?h3
  where 
    0 prf0 : (cadd (QSucc (Fin m')) n === QSucc (cadd (Fin m') n)) 
    prf0 = caddOutLeft
-}
public export
join : {1 m : CNat} -> (0 prf : Finite m) => Mu m (Mu n t w) x -@ Mu (m * n) t w
joinFin : {1 m : QNat} -> Mu (Fin m) (Mu n t w) x -@ Mu ((Fin m) * n) t w
joinFin {m=Zero} MZ = let 
  res : Mu 0 t w = MZ
  in rewrite cmulZeroLeft {y=n} in res
joinFin {m=Succ m'} x' = ?jf
{-
join MZ = rewrite cmulZeroLeft {y=n} in MZ
join {m'} {n=n} (MS x xs) = rewrite prf0 in combine x (the (Mu (m' * n) t w) (join xs))
  where 
    0 prf0 : (lmul (Succ m') n = n + lmul m' n)
    prf0 = rewrite mulRep in Refl
-}
