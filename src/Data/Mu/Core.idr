module Data.Mu.Core
import Data.Mu.Types

import Data.Mu.Util.Relude
import Data.Mu.Util.Nat
import Data.Mu.Util.Types
import Data.Nat
--import Data.Qty
import Prelude.Types
import Data.Mu.Util.LPair
import Data.Mu.Util.LPair as LExists
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
map : (f : t -@ u) -> Mu n t w -@ Mu n u (f w)
map f MZ = MZ
map f (MS x xs) = MS (f x) (map {w=x} f xs)

private 
applyPair : (LPair (t -@ u) (t)) -@ (u)
applyPair (f # x) = f x
public export 
app : Mu n (t -@ u) wf -@ Mu n t wx -@ Mu n u (wf wx)
app MZ MZ = MZ 
app (MS f fs) (MS x xs) = MS (f x) (app fs xs)
  
----------------------------------------------------------------
-- Operations on Mu
----------------------------------------------------------------

namespace Mu
    public export
    combine : forall t, n, m. {0 w : t} -> Mu n t w -@ Mu m t w -@ Mu (ladd n m) t w
    combine {w} MZ ys = ys
    combine {w=x} (MS x xs) ys = MS x  (combine xs ys)

    
    public export
    split : forall t, w, n. {1 m : LNat} -> Mu (ladd m n) t w -@ LPair (Mu m t w) (Mu n t w)
    split {m=Zero} xs = MZ # xs
    split {m=Succ m} (MS x xs) = let (ys # zs) = split {m=m} ( xs) in (MS x ys # zs)
    public export 
    split' : forall t, w. {1 m : LNat} -> {0 n : LNat} -> {0 c : LNat} -> (0 prf : c === ladd m n) -> Mu c t w -@ LPair (Mu m t w) (Mu n t w)
    split' {m=m} {c=c} {n=n} prf xs = split {m=m} {n=n} (rewrite sym prf in xs)
    ||| Context multiplication
    public export 
    squash : forall t, n, m. {0 w : t} -> {0 w' : ?} -> Mu n (Mu m t w) w' -@ Mu (lmul n m) t w
    squash MZ = ?smu
    squash (MS x xs) = ?smu2
    ||| Context deriliction
    public export
    expand : {1 n : LNat} -> {0 w : t} -> Mu (lmul n m) t w -@ Mu n (Mu m t w) (Example m w)
    -- expand {n=Zero} MZ = ?em2
    -- expand {n=Succ n} x = ?em
    
    public export 
    0 witness : Mu n t w -> t
    witness {w=w} _ = w
    public export 
    once : Mu (Succ Zero) t w -@ t
    once (MS x MZ) = x
    public export
    reactM : forall t, u, n1. 
        {0 w : t} -> {0 w' : u} -> 
        {1 m : LNat} -> 
        {1 n0 : LNat} ->
        {0 fw : ?} -> 
        (Mu m ((Mu n0 t w) -@ (Mu n1 u w')) fw) -@ 
        (Mu (lmul m n0) t w) -@ 
        (Mu (lmul m n1) u w')
    reactM {m=Zero} {n0=n0} MZ x = let 
            0 prf0 : (lmul Zero n0) === Zero
            prf0 = lmul_zero_left
            0 prf1 : (lmul Zero n1) === Zero
            prf1 = lmul_zero_left
            res : Mu (lmul Zero n1) u w'
            res = rewrite prf1 in MZ
        in seq n0 (seq (consumeZero prf0 x) res)
    reactM {m=Succ m} {n0=n0} (MS f fs) x = let 
            (x' # xs) = split' {m=n0} lmul_succ_left x
        in ?r0
        
    public export
    log : {0 a : Type} -> (1 ex : (a ^^ n)) -> Mu n a (LExists.fst ex)
    log {a=a} ex = LExists.snd ex
    public export 
    exp : {0 a : Type} -> {0 w : a} -> Mu n a w -@ (a ^^ n)
    exp {a} {w} x = LEvidence w x

   
namespace Exp

