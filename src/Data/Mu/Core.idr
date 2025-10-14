module Data.Mu.Core

import Data.Mu.Types

import Data.Mu.Util.Relude
import Data.Mu.Util.Nat
import Data.Mu.Util.Types
--import Data.Nat
import Data.Mu.Util.LPair
import Data.Mu.Util.LPair as LExists
----------------------------------------------------------------
-- Basic
----------------------------------------------------------------

public export 
push : forall t, u, w0, w1, n. Mu n (LPair t u) (w0 # w1) -@ (LPair (Mu n t w0) (Mu n u w1))
push MZ = MZ # MZ
push (MS (x # y) z) = let (xs # ys) = push z in (MS x  xs # MS y  ys)
public export 
pull : forall t, u, w0, w1, n. (LPair (Mu n t w0) (Mu n u w1)) -@ Mu n (LPair t u) (w0 # w1)
pull (MZ # MZ) = MZ
pull (MS x xs # MS y ys) = MS (x # y)  (pull (xs # ys))
public export 
map : (f : t -@ u) -> Mu n t w -@ Mu n u (f w)
map f MZ = MZ
map f (MS x xs) = MS (f x) (map {w=x} f xs)

private 
applyPair : (LPair (t -@ u) (t)) -@ (u)
applyPair (f # x) = f x
public export 
app : Mu n (t -@ u) wf -> Mu n t wx -@ Mu n u (wf wx)
app MZ MZ = MZ 
app (MS f fs) (MS x xs) = MS (f x) (app fs xs)
  
----------------------------------------------------------------
-- Operations on Mu
----------------------------------------------------------------

namespace Mu
    public export
    combine : forall t, n, m. {0 w : t} -> Mu n t w -@ Mu m t w -@ Mu (n + m) t w
    combine {w} MZ ys = ys
    combine {w=x} (MS x xs) ys = MS x  (combine xs ys)

    
    public export
    split : forall t, w, n. {1 m : Nat} -> Mu (m + n) t w -@ LPair (Mu m t w) (Mu n t w)
    split {m=Z} xs = MZ # xs
    split {m=S m} (MS x xs) = let (ys # zs) = split {m=m} ( xs) in (MS x ys # zs)
    public export 
    split' : forall t, w. {1 m : Nat} -> {0 n : Nat} -> {0 c : Nat} -> {auto 0 prf : c === m + n} -> Mu c t w -@ LPair (Mu m t w) (Mu n t w)
    split' {m=m} {c=c} {n=n} xs @{prf} = split {m=m} {n=n} (rewrite sym prf in xs)
    ||| Context multiplication
    public export 
    squash : forall t, n, m. {0 w : t} -> {0 w' : ?} -> Mu n (Mu m t w) w' -@ Mu (n * m) t w
    squash MZ = MZ
    squash (MS x xs) = combine x (squash xs)
    ||| Context deriliction
    public export
    expand : {1 n : Nat} -> {0 w : t} -> Mu (n * m) t w -@ Mu n (Mu m t w) (example m w)
    expand {n=Z} MZ = MZ
    expand {n=S n} x = ?em
    
    public export 
    0 witness : Mu n t w -> t
    witness {w=w} _ = w
    public export 
    once : Mu 1 t w -@ t
    once (MS x MZ) = x
    public export
    react : forall t, u, n0, n1. 
      {0 w : t} -> {0 w' : u} -> {0 fw : ?} -> {1 m : Nat} -> 
      (Mu m ((Mu n0 t w) -@ (Mu n1 u w')) fw) -@ 
      (Mu (n0 * m) t w) -@ 
      (Mu (n1 * m) u w')
    react {m=Z} f x = ?h5
    react {m=S m'} _ _ = ?h6
    public export
    log : {0 a : Type} -> (1 ex : (a ^^ n)) -> Mu n a (LExists.fst ex)
    log {a=a} ex = LExists.snd ex
    public export 
    exp : {0 a : Type} -> {0 w : a} -> Mu n a w -@ (a ^^ n)
    exp {a} {w} x = LEvidence w x

   
namespace Exp

public export
{0 w : t} -> Drop (Mu 0 t w) where 
    drop MZ = ()
