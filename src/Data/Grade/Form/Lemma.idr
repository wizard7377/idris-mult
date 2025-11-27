module Data.Grade.Form.Lemma
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
  reflexive x {n} = x
||| If p <: q and q <: r then p <: r
public export
Transitive Form Unify where 
	transitive p0 p1 x = let 
            r0 = p0 x
            r1 = p1 r0
	  in r1

  
public export
0 SolveLiteral : Solve (FVal n) n 
SolveLiteral = Elem [] Refl

public export
0 LiteralSolve : {x : QNat} -> Solve (FVal n) x => (x = n)
LiteralSolve @{Elem v prf} = ?hls
%hint
public export  
FVarInit : {p : Form} -> Unify FVar p
FVarInit x = ?hfvi
{-

THEOREMS ON FORMULAS

-}
private 
0 CombineAdd : {a, b,c,d : QNat} -> (a = c) -> (b = d) -> (a + b = c + d)
CombineAdd Refl Refl = Refl
export
0 AppAddVars : (0 p, q : Form) -> (FApp op p q).vars = p.vars + q.vars
export 
0 EvalOp : 
    {op : FOp} ->
    {n1, n2 : QNat} ->
    {p : Form' n1} -> 
    {q : Form' n2} -> 
    {v1 : QVect n1 QNat} ->
    {v2 : QVect n2 QNat} ->
    (Eval' (FApp' op p q) (append v1 v2) = runOp op (Eval' p v1) (Eval' q v2)) 
export
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
export      
SplitOp' : {1 m : QNat} -> {1 p : Form' m} -> {1 q : Form' n} -> Solve' (FApp' op p q) z -@ ((x : QNat) #? ((y : QNat) #? (Solve' p x `LPair` (Solve' q y `LPair` (Erase (runOp op x y = z))))))
SplitOp' {m} (Elem v_z prf_z) = let 
    1 (v_z_0 # v_z_1) = Form.Types.splitAt m v_z
    0 v_r_0 : QNat = Eval' p v_z_0
    0 v_r_1 : QNat = Eval' q v_z_1
    0 v_prf_0 : Eval' p v_z_0 === v_r_0 = believe_me ()
    0 v_prf_1 : Eval' q v_z_1 === v_r_1 = believe_me ()
    0 prf_r : runOp op v_r_0 v_r_1 === z = ?hs0
  in Given v_r_0 (Given v_r_1 ((Elem v_z_0 v_prf_0) # (Elem v_z_1 v_prf_1) # (MkErase prf_r)))

export 
SplitOp : (0 prf : Solve (FApp op p q) z) => (Sigma QNat $ \x => Subset QNat $ \y => (Sigma (Solve p x) $ \_ => Sigma (Solve q y) $ \_ => runOp op x y = z))
SplitOp @{Elem v_z prf_z} = ?so

export 
0 NotSplitOp' : {p : Form' m} -> {q : Form' n} -> {z : QNat} -> Not (Solve' (FApp' op p q) z) -> Not ((x : QNat) #? ((y : QNat) #? (Solve' p x, Solve' q y, runOp op x y = z)))
NotSplitOp' pf (Given v_r_0 (Given v_r_1 ((Elem v_z_0 v_prf_0), (Elem v_z_1 v_prf_1), prf_r))) {z} = let 
    v_z = append v_z_0 v_z_1
    prf_z : Eval' (FApp' op p q) v_z === z = ?hs1
  in pf (Elem v_z prf_z)

export 
0 NotSplitOp : {p, q : Form} -> {z : QNat} -> Not (Solve (FApp op p q) z) => Not ((x : QNat) #? ((y : QNat) #? (Solve p x, Solve q y, runOp op x y = z)))
NotSplitOp @{pf} = ?nso2

%hint 
export 
0 EvalReduce : ((Eval p x) = y) => (Solve p y)
%hint
export 
0 EqValue : Solve (FVal n) x => (x = n)
EqValue @{Elem v prf} = ?eqv
