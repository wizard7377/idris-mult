module Data.Grade.Omega.Ops


import Data.Grade.Util.Relude
import Data.Grade.Mu.Ops
import Data.Grade.Mu.Types
import Data.Grade.Form
import Data.Grade.Omega.Types
import Decidable.Equality
import Data.Grade.Set
import Data.Linear.LVect
import Data.Grade.Mu.Lemma
import Prelude.Ops
import Data.Grade.Util.Linear
import Control.Function.FunExt
import Data.Grade.Util.Unique

%default total


namespace Omega
    ||| Given that we have p ⊑ q, we can weaken an Omega p t w to an Omega q t w
    ||| We do this by using the evidence from Unify q p to convert the Mu (Eval p n) t w to Mu (Eval q n) t w
    public export
    weaken : (1 x : Omega p t w) -> (1 prf : Unify q p) => Omega q t w
    weaken x @{prf} {t} n = let 
        1 (Element ex prf') = prf n
        1 x' : Mu (Eval p ex) t w = x ex
        in rewrite prf' in x'
    ||| Convert an Omega p t w to Mu n t w, given a proof that p is solvable at n
    ||| This is different from simply applying n.
    ||| Rather then getting the result of the formula at n, we get exactly n, so long as we have some input that evaluates p to n
    public export
    reify : 
        (1 x : Omega p t w) -> 
        (1 prf : Solve p n) => 
        Mu n t w
    reify x @{(Element n' prf)} {t} = rewrite sym prf in x n'
    ||| Omega is unique up to equality 
    public export
    uniqueOmega : forall p, t, w. Unique (Omega p t w)
    uniqueOmega = ?uo
    ||| A "simple" mapping of a linear function over Omega.
    ||| This is different from Omega.map in that the function is unrestricted, so we mark it as unsafe, to keep with the notion of a "completly" linear system
    %unsafe
    private
    simpleMapOmega : 
        (f : t -@ u) -> 
        Omega p t w -@ 
        Omega p u (f w)
    simpleMapOmega f x {n} = Mu.Ops.map f (x {n})
    ||| Map a linear function over a value by distributing it through the Omega
    ||| Roughly equivalent to the fact that `(a -> b) [n] -> a [n] -> b [n]` in GrTT
    public export
    map : 
        Omega p (t -@ u) wf -@
        Omega p t wx -@
        Omega p u (wf wx)
    map f x {n} = let 
        1 [n0,n1] = n.clone 2 
        in app (f $$ n0) (x $$ n1)
    ||| Expand an Omega of the form Omega (k * p) t w to Omega p (Mu k t w) (Repeat w)
    public export
    expand :

        {1 k : QNat} ->
        {1 p : Form} -> 
        Omega (FApp (FMul FVar (Lit k)) p) t w -@ 
        Omega p (Mu k t w) (Repeat w)
    expand {k} x {n} = let 
        1 [n0, n1] = n.clone 2
        1 x0 : (Mu (lmul (Eval p n) k) t w) = x $$ n0
        1 x1 : (Mu (lmul (Eval' p n) k) t w) = rewrite n1.prf in (rewrite eval_eq {f=p} {x=n1.val} in (rewrite sym n1.prf in x0))
        1 y0 : (Mu (Eval' p n) (Mu k t w) (Example k w)) = rewrite n1.prf in expand {m=(Eval' p $ n1.val)} {n=k} (rewrite sym n1.prf in x1)
        1 y1 : (Mu (Eval p n) (Mu k t w) (Example k w)) = rewrite sym $ eval_eq {f=p} {x=n} in y0
        0 prf1 : (Example k w === Repeat w) = uniqueEq 
        1 y2 : Mu (Eval p n) (Mu k t w) (Repeat w) = rewrite sym prf1 in y1
        in y2
    ||| Squash an Omega of the form Omega p (Mu k t w) (Repeat w) to Omega (k * p) t w
    public export
    squash : 
        {1 k : QNat} ->
        {1 p : Form} -> 
        Omega p (Mu k t w) (Repeat w) -@ 
        Omega ((FVar #*# (### k)) #*# p) t w
    squash {k} x {n} = ?h0
    ||| An alias for `map`
    public export 
    app : Omega p (t -@ u) wf -@ Omega p t wx -@ Omega p u (wf wx) 
    app f x = Omega.map f x
    ||| Fully general Omega application, of the form `(a [m] -> b) [n] -> a [m*n] -> b [n]`
    ||| A useful application of this is `(a [m] -> b [m']) [n] -> a [m*n] -> b [m'] [n]`, which directly follows
    public export
    react : 
        forall t, w, u.
        {1 p : Form} ->
        {1 k : QNat} ->
        {0 wf : (Mu k t w) -@ u} ->
        Omega p ((Mu k t w) -@ u) wf -@
        Omega ((FVar * (FVal k)) #$# p) t w -@
        Omega p u (wf (Example k w))
    react f x = let 
        1 x' : Omega p (Mu k t w) (Example k w) = rewrite uniqueEq {x=Example k w} in Omega.expand x
        in Omega.app f x'
