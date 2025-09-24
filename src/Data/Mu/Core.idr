module Data.Mu.Core

import Data.Mu.Types

import Data.Mu.Util.Relude
import Data.Mu.Util.Nat
import Prelude.Ops

----------------------------------------------------------------
-- Higher Order Functions 
----------------------------------------------------------------

export 
mapSource : {0 t, u : Type} -> {0 x : t} -> (f : t -@ u) -> Source {t=t} n x -@ Source {t=u} n (f x)
mapSource {t=t} {u=u} {x=x} f (Exhaust {t=t} {x=x}) = Exhaust
mapSource {t=t} {u=u} {x=x} f (Provide {t=t} {n=n} x xs) = Provide (f x) (mapSource f xs)
  
public export
mapM : {0 t, u : Type} -> (f : t -@ u) -> M n t -@ M n u
mapM {t=t} {u=u} f (Supply w s) = Supply (f w) (mapSource f s)



----------------------------------------------------------------
-- Operations on Source
----------------------------------------------------------------


public export
combine' : Source {t=t} n x -@ Source {t=t} m x -@ Source {t=t} (n + m) x
combine' (Exhaust {t=t} {x=x}) ys = ys
combine' (Provide {t=t} {n=n} x xs) ys = Provide x (combine' xs ys)

private
split'' : {0 m : Nat} -> (1 n : Nat) -> Source {t=t} (m + n) x -@ LPair (Source {t=t} m x) (Source {t=t} n x)

public export 
split' : {0 m, c : Nat} -> {1 n : Nat} -> {auto 0 prf : c === m + n} -> Source {t=t} c x -@ LPair (Source {t=t} m x) (Source {t=t} n x)
split' {m=m} {c=c} {n=n} xs @{prf} = split'' {m=m} n (rewrite sym prf in xs)
  
public export 
squash' : {0 x : t} -> {0 y : Source {t=t} n x} -> Source m y -@ Source (n * m) x
squash' {x=x} {y=y} (Exhaust {t=Source {t=t} n x} {x=y}) = rewrite multZeroRightZero n in Exhaust
squash' {x=x} {y=y} (Provide {t=Source {t=t} n x} {n=m} y ys) = rewrite multSuccAdd {a=n} {b=m} in combine' y (squash' {x=x} {y=y} ys) 

public export
expand' : {0 n, m : Nat} -> Source (n * m) x -@ Source n (Source m x)
----------------------------------------------------------------
-- Operations on M
----------------------------------------------------------------

public export 
combine : (1 x : M m t) -> (1 y : M n t) -> {auto 0 prf : Like x y} -> M (m + n) t
combine (Supply w0 s0) (Supply w1 s1) @{prf} = Supply w0 (combine' s0 (rewrite prf in s1))

public export
split : {0 m, n, c : Nat} -> {auto 0 prf : c === m + n} -> (1 x : M c t) -> (LPair (M m t) (M n t))
split (Supply _ Exhaust) @{prf} = ((rewrite fst prf' in exhaust) # (rewrite snd prf' in exhaust))
  where 
    0 prf' : (m === 0, n === 0)
    prf' = plusZeroBoth {a=m} {b=n} @{sym prf}
split {m, n} (Supply x (Provide x xs)) @{prf} = ?h32
  
public export
squash : {0 m, n : Nat} -> (1 x : M m (M n t)) -> M (m * n) t


public export
expand : {0 m, n : Nat} -> (1 x : M (m * n) t) -> M m (M n t)
expand = ?h4


----------------------------------------------------------------
-- Operations on W
----------------------------------------------------------------

public export
unW : {0 p : Proj} -> {1 n : Nat} -> (1 x : W p t) -> M (p n) t
unW {n} x = x {n}
public export
reify : {0 p : Proj} -> {0 n : Nat} -> {auto 0 prf : MapTo p n} -> (1 x : W p t) -> M n t
----------------------------------------------------------------
-- Constructions 
----------------------------------------------------------------
private
genMany' : {0 t : Type} -> (x : t) -> (1 n : Nat) -> Source n x
genMany' {t=t} x Z = Exhaust 
genMany' {t=t} x (S n) = (Provide x (Delay (genMany' {t=t} x n)))
private 
genMany : {0 t : Type} -> (x : t) -> (1 n : Nat) -> M n t
genMany {t=t} x n = Supply x (genMany' {t=t} x n)

public export
genW : {0 t : Type} -> {1 p : Proj} -> ((x : t) -> W p t)
genW {t=t} {p=p} x n = Supply x (genMany' {t=t} x (p n))

public export 
genM : {0 t : Type} -> (x : t) -> (1 n : Nat) -> M n t
genM {t=t} x n = genMany {t=t} x n
