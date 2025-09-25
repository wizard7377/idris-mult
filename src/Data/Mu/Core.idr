module Data.Mu.Core

import Data.Mu.Types

import Data.Mu.Util.Relude
import Data.Mu.Util.Nat
import Prelude.Ops

%unbound_implicits off
----------------------------------------------------------------
-- Higher Order Functions 
----------------------------------------------------------------

export 
mapM : forall n, t, u. {0 w : t} -> (f : t -@ u) -> M n t {w} -@ M n u {w=f w}
mapM f MZ = MZ
mapM {w=x} f (MS x xs) = MS {w = (f x)} (f x) (mapM {w=x} f xs)


----------------------------------------------------------------
-- Operations on M
----------------------------------------------------------------


public export
combine : forall t, n, m. {0 w : t} -> M n t {w} -@ M m t {w} -@ M (n + m) t {w}
combine {w=w} MZ ys = ys
combine {w=x} (MS x xs) ys = MS {w=x} x (combine xs ys)


public export
split' : forall t, w. {1 m : Nat} -> {0 n : Nat} -> M (m + n) t {w} -@ LPair (M m t {w}) (M n t {w})
split' {m=Z} xs = MZ # xs
split' {m=S m} (MS x xs) = let (ys # zs) = split' {m=m} (Force xs) in (MS {w=x} x ys # zs)
public export 
split : forall t, w. {1 m : Nat} -> {0 n : Nat} -> {0 c : Nat} -> {auto 0 prf : c === m + n} -> M c t {w} -@ LPair (M m t {w}) (M n t {w})
split {m=m} {c=c} {n=n} xs @{prf} = split' {m=m} {n=n} (rewrite sym prf in xs)
public export 
squash : forall t, n, m. {0 w : t} -> {0 w' : ?} -> M n (M m t {w}) {w=w'} -@ M (n * m) t {w}
squash MZ = MZ
squash (MS x xs) = combine x (squash xs)

----------------------------------------------------------------
-- Operations on W
----------------------------------------------------------------

export
genW : {0 t : Type} -> (1 src : (!* t)) -> (W IdProj t {w=(unrestricted src)})
genW {t=t} src 0 = seq src MZ
genW {t=t} (MkBang src) (S n) = MS {w=src} src (genW {t=t} (MkBang src) n)

export 
reify' : forall t. {0 p : Proj} -> {0 w : t} -> {n : Nat} -> W p t {w} -@ M (p n) t {w}
reify' {p=p} {n=n} {w=w} f = f n

export 
reify : forall t. {0 p : Proj} -> {0 w : t} -> {n : Nat} -> (1 _ : W p t {w}) -> {auto 0 prf : MapTo p n} -> M (p n) t {w}
