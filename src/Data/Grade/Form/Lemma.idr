module Data.Grade.Form.Lemma
import Data.Linear.Notation
import Data.Grade.Util.Linear
import Data.Linear.Interface
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
namespace Form 
    public export
    Id : Form
    Id = Over 1 FVar'
    public export
    Lit : QNat -@ Form
    Lit n = Over 0 $ FVal' n
||| p <: q
public export 
Reflexive Form Unify where 
  reflexive x = (Elem x Refl)
||| If p <: q and q <: r then p <: r
public export
Transitive Form Unify where 
	transitive p0 p1 x = let 
		1 (Elem y0 prf0) = p0 x
		1 (Elem z0 prf1) = p1 y0
		in Elem z0 (rewrite prf0 in prf1)
  
  
{-

THEOREMS ON FORMULAS

-}
private 
0 CombineAdd : {a, b,c,d : QNat} -> (a = c) -> (b = d) -> (a + b = c + d)
CombineAdd Refl Refl = Refl
0 AppAddVars : (0 p, q : Form) -> (FApp op p q).vars = p.vars + q.vars
 
0 EvalOp : 
    {op : FOp} ->
    {n1, n2 : QNat} ->
    {p : Form' n1} -> 
    {q : Form' n2} -> 
    {v1 : QVect n1 QNat} ->
    {v2 : QVect n2 QNat} ->
    (Eval' (FApp' op p q) (append v1 v2) = runOp op (Eval' p v1) (Eval' q v2)) 
0 SplitSolveOp : {z : QNat} -> {op : FOp} -> {p, q : Form} -> (((x : QNat) #? ((y : QNat) #? (Solve p x, Solve q y, runOp op x y = z))) <=> (Solve (FApp op p q) z))

SplitSolveOp {z} {op} {p} {q} = MkEquivalence fwd bck 
  where 
    fwd : (((x : QNat) #? ((y : QNat) #? (Solve p x, Solve q y, runOp op x y = z))) -> (Solve (FApp op p q) z)) 
    fwd 
      (Given x (Given y ((Elem v_p prf_p), (Elem v_q prf_q), prf_z))) = 
        Elem 
          (rewrite FAddVars {op=op} {p=p} {q=q} in append v_p v_q) 
          (let 
            0 prf' : Eval' ((FApp op p q) .form) (rewrite AppAddVars {op=op} p q in append v_p v_q) === z := ?hf0
            in prf'
          )
    bck : ((Solve (FApp op p q) z) -> ((x : QNat) #? ((y : QNat) #? (Solve p x, Solve q y, runOp op x y = z)))) 
    bck (Elem v_z prf_z) = ?hb
      
