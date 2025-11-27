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
import Data.Grade.Form.Sugar
import Prelude.Types
%default total


namespace Omega
    ||| Given that we have p ⊑ q, we can weaken an Omega p t w to an Omega q t w
    ||| We do this by using the evidence from Unify q p to convert the Mu (Eval' p n) t w to Mu (Eval' q n) t w
    public export
    weaken : (1 x : Omega p t w) -> (1 prf : Unify p q) => Omega q t w
    weaken x @{prf} {t} n = x n @{?h0}

    ||| Convert an Omega p t w to Mu n t w, given a proof that p is solvable at n
    ||| This is different from simply applying n.
    ||| Rather then getting the result of the formula at n, we get exactly n, so long as we have some input that evaluates p to n
    public export
    reify : 
        (1 x : Omega p t w) -> 
        {1 n : QNat} ->
        (0 prf : Solve p n) => 
        Mu n t w
    reify x {n} @{prf} = x {n} @{prf}
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
    simpleMapOmega f x {n} = Mu.Ops.map' f (x {n})
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
    
    ||| An alias for `map`
    public export 
    app : Omega p (t -@ u) wf -@ Omega p t wx -@ Omega p u (wf wx) 
    app f x = Omega.map f x
    public export
    combine : {0 p : Form} -> Omega p t w -@ Omega q t w -@ Omega (p |+| q) t w
    combine x y n @{prf} = seq n $ let 
        1 prf' = SplitOp {p=p,q=q,op=AddOp} @{prf}
        1 (For n1 (Elem n2 prf0)) = prf'
        0 prf_0_0 = Sigma.fst prf0
        0 prf_0_1 = Subset.snd prf_0_0
        0 prf_1_0 = Sigma.snd prf0
        0 prf_1_1 = Sigma.fst prf_1_0
        0 prf_1_2 = Subset.snd prf_1_1
        1 x' : (Mu n1 t w) = x n1 @{ (Elem (Subset.fst prf_0_0) prf_0_1) }
        1 y' : (Mu n2 t w) = y n2 @{ (Elem (Subset.fst prf_1_1) prf_1_2) } 
        1 z' : Mu (n1 + n2) t w = Mu.Ops.combine x' y'
        0 prf_s_eq : (n1 + n2 = n) = Sigma.snd (Sigma.snd prf0)
        in rewrite sym prf_s_eq in z'
