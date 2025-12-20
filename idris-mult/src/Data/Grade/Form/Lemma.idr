
import Data.Linear.Notation
import Data.Grade.Util.Linear
import Data.Linear.Interface
import Relude
import Data.Grade.QNat
import Prelude.Num
import Builtin
import Prelude.Types
import Data.Linear.LVect
import Data.Linear.LMaybe
import Data.Grade.Logic
import Prelude
import Control.Relation
import Data.Grade.Form.Types
import Data.Grade.Form.Ops

public export 
Reflexive Form Unify where 
  reflexive x {n} = x
||| If p <: q and q <: r then p <: r
public export
Transitive Form Unify where 
	transitive p0 p1 x = let 
            r0 = p0 x
            r1 = p1 r0
	  in r1

public export
Reflexive Form Equiv where 
  reflexive {x} = MkEquiv (reflexive {rel=Unify} {x}) (reflexive {rel=Unify} {x}) 

public export
Symmetric Form Equiv where 
  symmetric (MkEquiv p q) = MkEquiv q p 

public export
Transitive Form Equiv where 
    transitive p0 p1 = let 
            (MkEquiv p01 q01) = p0
            (MkEquiv p12 q12) = p1
      in MkEquiv (transitive {rel=Unify} p01 p12) (transitive {rel=Unify} q12 q01)
public export 
Equivalence Form Equiv where


--- BASIC LEMMAS 

%hint
export
lem_notBot : (FBot ?> n) -@ Void
lem_notBot prf impossible

%hint
export 
lem_alwaysTop : FTop ?> n
lem_alwaysTop = SolveTop

%hint 
export 
thm_botTerm : p :> FBot
thm_botTerm contra = linear_absurd $ lem_notBot contra

%hint 
export 
thm_topInit : FTop :> p
thm_topInit p = seq p (lem_alwaysTop)

%hint 
export 
lem_split : Solve (FAlt p q) n <=> (Either (Solve p n) (Solve q n))
lem_split = MkEquivalence go1 go2
  where 
    go1 : Solve (FAlt p q) n -> Either (Solve p n) (Solve q n)
    go1 (SolveAltLeft @{prf}) = Left prf
    go1 (SolveAltRight @{prf}) = Right prf
    go2 : Either (Solve p n) (Solve q n) -> Solve (FAlt p q) n
    go2 (Left prf) = SolveAltLeft @{prf}
    go2 (Right prf) = SolveAltRight @{prf}
%hint
export
cor_value : (FVal x ?> y) <=> (x === y)
cor_value = MkEquivalence go1 go2
    where
        go1 : (FVal x ?> y) -> (x === y)
        go1 (SolveVal @{prf}) = rewrite prf in Refl
        

        go2 : (x === y) -> (FVal x ?> y)
        go2 prf = SolveVal @{prf}

%hint 
export 
thm_gen_add : 
    (p' :> p) =@ 
    (q' :> q) =@
    (FAdd p' q' :> FAdd p q)
  
thm_gen_add @{prf_p'} @{prf_q'} (SolveAdd {n1, n2} @{prf_p} @{prf_q} @{prf_n} ) = let 
        1 prf_1 : Solve p' n1 = (prf_p' {n=n1}) prf_p
    
        1 prf_2 : Solve q' n2 = (prf_q' {n=n2}) prf_q
        in SolveAdd @{prf_1} @{prf_2} @{prf_n}
%hint 
export 
cor_gen_add_eq : 
    (p' :~: p) =@ 
    (q' :~: q) =@
    (FAdd p' q' :~: FAdd p q)
cor_gen_add_eq @{(MkEquiv prf_p_1 prf_p_2)} @{(MkEquiv prf_q_1 prf_q_2)} = MkEquiv (thm_gen_add @{prf_p_1} @{prf_q_1}) (thm_gen_add @{prf_p_2} @{prf_q_2})

export
rem_lift_solve : 
    {1 k : QNat} ->
    {1 n : QNat} -> 
    {0 p : Form} ->
    Solve p n =@
    SolveMany k p (k * n)
rem_lift_solve {k=Zero} @{prf} = seq n $ seq prf SolveNone
rem_lift_solve {k= Succ k'} @{prf} = let 
  1 [prf_1, prf_2] = prf.clone' @{ %search } @{CopyClone} 2
  1 prf_x : SolveMany k' p (k' * n) = rem_lift_solve @{prf_1.val}
  0 prf_n : ((Succ k') * n === n + (k' * n)) = lmul_succ_left 
  in SolveSome {x=n} {y=(lmul k' n)} @{prf_2.val} @{ prf_x } @{ (rewrite prf_n in Refl) } 
%hint 
export
thm_gen_mul : 
    (p' :> p) =@ 
    (q' :> q) =@
    (FMul p' q' :> FMul p q)
thm_gen_mul @{prf_p'} @{prf_q'} (SolveMul {x} @{prf_x} @{prf_n}) = SolveMul @{ prf_p' prf_x } @{ ?thm_gen_mul_rhs_2 }

private 
thm_add_comm_1 : FAdd p q :> FAdd q p
thm_add_comm_1 (SolveAdd {n1, n2} @{prf_p} @{prf_q} @{prf_n}) =  
  SolveAdd {n1=n2, n2=n1} @{prf_q} @{prf_p} @{ ?prf_n_mod }
 
%hint 
export 
thm_add_comm : 
    (FAdd p q :~: FAdd q p)
thm_add_comm = MkEquiv thm_add_comm_1 thm_add_comm_1
        
private
Trailhead_1 : {1 p, q : Form} -> (1 prf : Path _ p q) -> p :> q
Trailhead_1 {p,q} path = ?trailhead_1_rhs

private 
Trailhead_2 : {1 p, q : Form} -> (1 prf : Path _ p q) -> q :> p
Trailhead_2 {p,q} path = ?trailhead_2_rhs

%hint
export
Trailhead : {1 p, q : Form} -> (1 prf : Path _ p q) -> (p :~: q)
Trailhead {p,q} prf = ?trailhead_equiv_rhs
  
private 
Pathfinder_1 : {1 p, q : Form} -> (1 prf : p :> q) -> Path _ p q

private 
Pathfinder_2 : {1 p, q : Form} -> (1 prf : q :> p) -> Path _ p q
%hint
export
Pathfinder : {1 p, q : Form} -> (1 prf : p :~: q) -> Path _ p q
