||| Ω is so special it gets its own file ;)
module Data.Mu.Omega
import Data.Mu.Types
import Data.Mu.Util.Relude
import Data.Mu.Core 
import Data.Mu.Set
import Data.Linear.LVect
import Data.Mu.Lemma
import Prelude.Ops
import Data.Mu.Util.Linear
import Control.Function.FunExt
import Data.Mu.Util.Unique
public export
weaken : (1 x : Omega p t w) -> (1 prf : Unify q p) => Omega q t w
weaken x @{prf} {t} n = let 
  1 (LSubset.LEvidence ex prf') = prf n
  1 x' : Mu (Eval p ex) t w = x ex
  in rewrite prf' in x'

public export
uniqueOmega : forall p, t, w. Unique (Omega p t w)
uniqueOmega = ?uo
private
simpleMapOmega : 
  (f : t -@ u) -> 
  Omega p t w -@ 
  Omega p u (f w)
simpleMapOmega f x {n} = Mu.Core.map f (x {n})

public export
mapOmega : 
    Omega p (t -@ u) wf -@
    Omega p t wx -@
    Omega p u (wf wx)
mapOmega f x {n} = let 
  1 [n0,n1] = n.clone 2 
  in app (f $$ n0) (x $$ n1)
  
public export
expandOmega :
            
    {1 k : LNat} ->
    {1 p : Form} -> 
    Omega (FApp (FMul FVar (Lit k)) p) t w -@ 
    Omega p (Mu k t w) (Repeat w)
expandOmega {k} x {n} = let 
  1 [n0, n1] = n.clone 2
  1 x0 : (Mu (lmul (Eval p n) k) t w) = x $$ n0
  1 x1 : (Mu (lmul (Eval' p n) k) t w) = rewrite n1.prf in (rewrite eval_eq {f=p} {x=n1.val} in (rewrite sym n1.prf in x0))
  1 y0 : (Mu (Eval' p n) (Mu k t w) (Example k w)) = rewrite n1.prf in expand {m=(Eval' p $ n1.val)} {n=k} (rewrite sym n1.prf in x1)
  1 y1 : (Mu (Eval p n) (Mu k t w) (Example k w)) = rewrite sym $ eval_eq {f=p} {x=n} in y0
  0 prf1 : (Example k w === Repeat w) = uniqueEq 
  1 y2 : Mu (Eval p n) (Mu k t w) (Repeat w) = rewrite sym prf1 in y1
  in y2

