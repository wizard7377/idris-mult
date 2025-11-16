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
import Data.Grade.Util.LPair
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
  reflexive x = (Element x Refl)
||| If p <: q and q <: r then p <: r
public export
Transitive Form Unify where 
	transitive p0 p1 x = let 
		1 (Element y0 prf0) = p0 x
		1 (Element z0 prf1) = p1 y0
		in Element z0 (rewrite prf0 in prf1)
  
  
{-

THEOREMS ON FORMULAS

-}
private 
0 CombineAdd : {a, b,c,d : QNat} -> (a = c) -> (b = d) -> (a + b = c + d)
CombineAdd Refl Refl = Refl
0 AppAddVars : (FApp op p q).vars = p.vars + q.vars
 
0 EvalOp : 
    {op : FOp} ->
    {n1, n2 : QNat} ->
    {p : Form' n1} -> 
    {q : Form' n2} -> 
    {v1 : QVect n1 QNat} ->
    {v2 : QVect n2 QNat} ->
    (Eval' (FApp' op p q) (append v1 v2) = runOp op (Eval' p v1) (Eval' q v2)) 
0 SplitSolveOp : (prf0 : Solve p x) -> (prf1 : Solve q y) -> {op : FOp} -> Solve (FApp op p q) (runOp op x y)
SplitSolveOp (Element x' prf0) (Element y' prf1) {op=op} = let
        vars : (QVect (FApp op p q).vars QNat) = (rewrite AppAddVars {op=op} {p=p} {q=q} in append x' y') 
        input = append x' y'
        res : (Eval' (FApp op p q).form vars = runOp op (Eval' p.form x') (Eval' q.form y')) = ?sso
    in Element vars (rewrite sym prf1 in rewrite sym prf0 in res)
