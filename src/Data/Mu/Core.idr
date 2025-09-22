module Data.Mu.Core

import Data.Mu.Types

import Data.Mu.Util.Relude
import Data.Mu.Util.Nat

----------------------------------------------------------------
-- Operations on Source
----------------------------------------------------------------

public export
combine' : Source {t=t} n x -@ Source {t=t} m x -@ Source {t=t} (n + m) x
combine' (Exhaust {t=t} {x=x}) ys = ys
combine' (Provide {t=t} {n=n} x xs) ys = Provide x (combine' xs ys)

public export
split' : {0 a, b : Nat} -> {auto 0 prf : (LTE b a)} -> Source {t=t} a x -@ (LPair (Source {t=t} b x) (Source {t=t} (safeMinus a b @{prf}) x))
split' (Exhaust {t=t} {x=x}) @{prf} = (rewrite (lteSquash @{prf}) in Exhaust) # Exhaust
split' (Provide {t=t} {n=n} x xs) @{prf} = ?h0

public export 
squash' : {0 x : t} -> {0 y : Source {t=t} n x} -> Source m y -@ Source (n * m) x
squash' {x=x} {y=y} (Exhaust {t=Source {t=t} n x} {x=y}) = rewrite multZeroRightZero n in Exhaust
squash' {x=x} {y=y} (Provide {t=Source {t=t} n x} {n=m} y ys) = rewrite multSuccAdd {a=n} {b=m} in combine' y (squash' {x=x} {y=y} ys) 


----------------------------------------------------------------
-- Operations on M
----------------------------------------------------------------

public export 
combine : (1 x : M m t) -> (1 y : M n t) -> {auto 0 prf : Like x y} -> M (m + n) t
combine (Supply w0 s0) (Supply w1 s1) @{prf} = Supply w0 (combine' s0 (rewrite prf in s1))

public export
split : {0 m, n : Nat} -> {auto 0 prf : (LTE n m)} -> (1 x : M m t) -> (LPair (M n t) (M (safeMinus m n @{prf}) t))
split @{prf} (Supply w s) = let (s1 # s2) = split' @{prf} s in (Supply w s1) # (Supply w s2)

public export
squash : {0 m, n : Nat} -> (1 x : M m (M n t)) -> M (m * n) t
squash = ?h2
