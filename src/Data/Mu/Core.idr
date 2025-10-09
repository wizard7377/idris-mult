module Data.Mu.Core

import Data.Mu.Types

import Data.Mu.Util.Relude
import Data.Mu.Util.Nat
import Prelude.Ops
import Data.Mu.Util.LPair
----------------------------------------------------------------
-- Basic
----------------------------------------------------------------

public export 
pushM : forall t, u, w0, w1, n. Mu n (LPair t u) (w0 # w1) -@ (LPair (Mu n t w0) (Mu n u w1))
pushM MZ = MZ # MZ
pushM (MS (x # y) z) = let (xs # ys) = pushM z in (MS x {w=x} xs # MS y {w=y} ys)
public export 
pullM : forall t, u, w0, w1, n. (LPair (Mu n t w0) (Mu n u w1)) -@ Mu n (LPair t u) (w0 # w1)
pullM (MZ # MZ) = MZ
pullM (MS x xs # MS y ys) = MS (x # y) {w=(x # y)} (pullM (xs # ys))
public export 
mapM : forall n, t, u. {0 w : t} -> (f : t -@ u) -> Mu n t w -@ Mu n u (f w)
mapM f MZ = MZ
mapM f (MS x xs) = MS {w = (f x)} (f x) (mapM {w=x} f xs)

private 
applyPair : (LPair (t -@ u) (t)) -@ (u)
applyPair (f # x) = f x
public export 
applyM : forall n, t, u, wf, wx. Mu n (t -@ u) wf -> Mu n t wx -@ Mu n u (wf wx)
applyM f x = 
  let 
    fx = pullM (f # x)
    y = mapM applyPair fx
  in y
  
  
----------------------------------------------------------------
-- Operations on Mu
----------------------------------------------------------------

namespace Mu
    public export
    combine : forall t, n, m. {0 w : t} -> Mu n t w -@ Mu m t w -@ Mu (n + m) t w
    combine {w} MZ ys = ys
    combine {w=x} (MS x xs) ys = MS x {w=x} (combine xs ys)


    public export
    split' : forall t, w, n. {1 m : Nat} -> Mu (m + n) t w -@ LPair (Mu m t w) (Mu n t w)
    split' {m=Z} xs = MZ # xs
    split' {m=S m} (MS x xs) = let (ys # zs) = split' {m=m} ( xs) in (MS x {w=x} ys # zs)
    public export 
    split : forall t, w. {1 m : Nat} -> {0 n : Nat} -> {0 c : Nat} -> {auto 0 prf : c === m + n} -> Mu c t w -@ LPair (Mu m t w) (Mu n t w)
    split {m=m} {c=c} {n=n} xs @{prf} = split' {m=m} {n=n} (rewrite sym prf in xs)
    public export 
    squash : forall t, n, m. {0 w : t} -> {0 w' : ?} -> Mu n (Mu m t w) w' -@ Mu (n * m) t w
    squash MZ = MZ
    squash (MS x xs) = combine x (squash xs)

    public export
    eraseZero : Mu Z t w -@ () 
    eraseZero MZ = ()
    public export 
    0 getWitness : Mu n t w -> t
    getWitness {w=w} _ = w
    public export
    react : forall t, u, n0, n1. {0 w : t} -> {0 w' : u} -> {0 fw : ?} -> {1 m : Nat} -> (Mu m ((Mu n0 t w) -@ (Mu n1 u w')) fw) -@ (Mu (n0 * m) t w) -@ (Mu (n1 * m) u w')
    react {m=Z} f x = ?h5
    react {m=S m'} _ _ = ?h6
public export
log : {0 a : Type} -> (1 ex : (a ^ n)) -> Mu n a (prfExists ex)
log {a=a} ex = valExists ex
public export 
exp : {0 a : Type} -> {0 w : a} -> Mu n a w -@ (a ^ n)
exp {a} {w} x = LEvidence w x

namespace Exp

----------------------------------------------------------------
-- Operations on Omega
----------------------------------------------------------------
export
genW : {0 t : Type} -> (1 src : (!* t)) -> (Omega IdProj t {w=unrestricted src})
genW {t=t} src 0 = seq src MZ
genW {t=t} (MkBang src) (S n) = MS src {w=src} (genW {t=t} (MkBang src) n)

export 
reify' : forall t. {0 p : Proj} -> {0 w : t} -> {n : Nat} -> Omega p t {w} -@ Mu (p n) t w
reify' {p=p} {n=n} {w} f = f n

export 
reify : forall t. {0 p : Proj} -> {0 w : t} -> {n : Nat} -> (1 _ : Omega p t {w}) -> {auto 0 prf : MapTo p n} -> Mu (p n) t w

-- dimapW : (M m t w0 -@ M n u w1 -@ M o r w2) -> W p t w0 -@ W q u w1 -@ W  r (f w)
