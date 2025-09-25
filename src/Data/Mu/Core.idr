module Data.Mu.Core

import Data.Mu.Types

import Data.Mu.Util.Relude
import Data.Mu.Util.Nat
import Prelude.Ops

----------------------------------------------------------------
-- Basic
----------------------------------------------------------------

public export 
pushM : forall t, u, w0, w1, n. M n (LPair t u) (w0 # w1) -@ (LPair (M n t w0) (M n u w1))
pushM MZ = MZ # MZ
pushM (MS (x # y) z) = let (xs # ys) = pushM z in (MS x {w=x} xs # MS y {w=y} ys)
public export 
pullM : forall t, u, w0, w1, n. (LPair (M n t w0) (M n u w1)) -@ M n (LPair t u) (w0 # w1)
pullM (MZ # MZ) = MZ
pullM (MS x xs # MS y ys) = MS (x # y) {w=(x # y)} (pullM (xs # ys))
public export 
mapM : forall n, t, u. {0 w : t} -> (f : t -@ u) -> M n t w -@ M n u (f w)
mapM f MZ = MZ
mapM f (MS x xs) = MS {w = (f x)} (f x) (mapM {w=x} f xs)

private 
applyPair : (LPair (t -@ u) (t)) -@ (u)
applyPair (f # x) = f x
public export 
applyM : forall n, t, u, wf, wx. M n (t -@ u) wf -> M n t wx -@ M n u (wf wx)
applyM f x = 
  let 
    fx = pullM (f # x)
    y = mapM applyPair fx
  in y
  
  
----------------------------------------------------------------
-- Operations on M
----------------------------------------------------------------


public export
combine : forall t, n, m. {0 w : t} -> M n t w -@ M m t w -@ M (n + m) t w
combine {w} MZ ys = ys
combine {w=x} (MS x xs) ys = MS x {w=x} (combine xs ys)


public export
split' : forall t, w, n. {1 m : Nat} -> M (m + n) t w -@ LPair (M m t w) (M n t w)
split' {m=Z} xs = MZ # xs
split' {m=S m} (MS x xs) = let (ys # zs) = split' {m=m} ( xs) in (MS x {w=x} ys # zs)
public export 
split : forall t, w. {1 m : Nat} -> {0 n : Nat} -> {0 c : Nat} -> {auto 0 prf : c === m + n} -> M c t w -@ LPair (M m t w) (M n t w)
split {m=m} {c=c} {n=n} xs @{prf} = split' {m=m} {n=n} (rewrite sym prf in xs)
public export 
squash : forall t, n, m. {0 w : t} -> {0 w' : ?} -> M n (M m t w) w' -@ M (n * m) t w
squash MZ = MZ
squash (MS x xs) = combine x (squash xs)

----------------------------------------------------------------
-- Operations on W
----------------------------------------------------------------

export
genW : {0 t : Type} -> (1 src : (!* t)) -> (W IdProj t {w=unrestricted src})
genW {t=t} src 0 = seq src MZ
genW {t=t} (MkBang src) (S n) = MS src {w=src} (genW {t=t} (MkBang src) n)

export 
reify' : forall t. {0 p : Proj} -> {0 w : t} -> {n : Nat} -> W p t {w} -@ M (p n) t w
reify' {p=p} {n=n} {w} f = f n

export 
reify : forall t. {0 p : Proj} -> {0 w : t} -> {n : Nat} -> (1 _ : W p t {w}) -> {auto 0 prf : MapTo p n} -> M (p n) t w

inType : {0 a : Type} -> (1 ex : (a ^ n)) -> M n a ex.fst
inType {a=a} ex = sndL ex

inValue : {0 a : Type} -> {0 w : a} -> M n a w -@ (a ^ n)
inValue {a} {w} x = LEvidence {fst'=w} {snd'=x}
