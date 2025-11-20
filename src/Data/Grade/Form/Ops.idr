module Data.Grade.Form.Ops
import Data.Grade.Form.Types
import Data.Linear.Notation
import Data.Grade.Util.Linear
import Data.Linear.Interface
import Data.Grade.QNat
import Prelude.Num
import Builtin
import Prelude.Types
import Data.Linear.LMaybe
import Data.Grade.Logic
import Prelude
import Control.Relation
%hide Data.Linear.Copies.splitAt 
%hide Data.Linear.LVect.splitAt
public export
Eval' : (1 f : Form' n) -> (1 x : QVect n QNat) -> QNat
Eval' FVar' [x] = x
Eval' (FVal' n) [] = n
Eval' ((FApp' op) {a} f g) x = let 
    (x1 # x2) = splitAt a x 
  in (runOp op) (Eval' f $ x1) ((Eval' g) $ x2)
public export 
Eval : (1 f : Form) -> (1 x : QVect f.vars QNat) -> QNat
Eval (Over v f) x = assert_linear (\_ => Eval' f x) v

||| Solve the formula `f` for the value `n`, ∈
%inline 
public export
0 Solve : (1 f : Form) -> (1 n : QNat) -> Type
Solve f n = (Subset (QVect f.vars QNat) (\x => (Eval' f.form x === n)))
  
public export
0 SolveAbove : (1 f : Form) -> (1 n : QNat) -> Type
SolveAbove (Over v f) n = (Subset (QVect v QNat) (\x => (LLTE n (Eval' f x))))
public export
0 SolveBelow : (1 f : Form) -> (1 n : QNat) -> Type
SolveBelow (Over v f) n = (Subset (QVect v QNat) (\x => (LLTE (Eval' f x) n)))
||| That `f` is a less general form that `g`, that is, `g` maps to everything that `f` maps to
public export
0 Unify : Rel Form
Unify f g = (1 x : QVect f.vars QNat) -> (Subset (QVect g.vars QNat) (\y => (Eval' f.form x === Eval' g.form y)))

public export
0 Equiv : Rel Form
Equiv f g = (Unify f g, Unify g f)
  
%hint  
public export
equiv : Unify f g => Unify g f => Equiv f g
equiv @{uf} @{ug} = (uf, ug)

public export
0 EvalVal' : Eval' (FVal' n) [] = n
EvalVal' = Refl
public export
0 EvalVal : Eval (FVal n) [] = n
EvalVal = ?ev

public export
0 EvalVar' : (x : QNat) -> Eval' FVar' [x] = x
EvalVar' x = Refl
public export
0 EvalVar : (x : QNat) -> Eval (FVar) [x] = x
EvalVar x = ?ev2
public export
0 EvalApp' : 
    {op : FOp} ->
    {n1, n2 : QNat} ->
    {p : Form' n1} -> 
    {q : Form' n2} -> 
    {v1 : QVect n1 QNat} ->
    {v2 : QVect n2 QNat} ->
    (Eval' (FApp' op p q) (append v1 v2) = runOp op (Eval' p v1) (Eval' q v2))
EvalApp' = ?h0
 
