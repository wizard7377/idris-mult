
module Data.Grade.Form.Ops
import Data.Grade.Form.Types
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

public export
Eval' : (1 f : Form' n) -> (1 x : LVect n QNat) -> QNat
Eval' FVar [x] = x
Eval' (FVal n) x = seq x n
Eval' (FAdd {a} f g) x = let 
    (x1 # x2) = LVect.splitAt a x 
  in ladd (Eval' f $ x1) ((Eval' g) $ x2)
Eval' (FMul {a} f g) x = let 
    (x1 # x2) = LVect.splitAt a x 
  in lmul (Eval' f $ x1) ((Eval' g) $ x2)
Eval' (FMin {a} f g) x = let 
    (x1 # x2) = LVect.splitAt a x 
  in lmin (Eval' f $ x1) ((Eval' g) $ x2)
Eval' (FMax {a} f g) x = let 
    (x1 # x2) = LVect.splitAt a x 
  in lmax (Eval' f $ x1) ((Eval' g) $ x2)

public export 
Eval : (1 f : Form) -> (1 x : LVect f.vars QNat) -> QNat
Eval (Over v f) x = assert_linear (\_ => Eval' f x) v
||| Solve the formula `f` for the value `n`, ∈
public export
0 Solve : (1 f : Form) -> (1 n : QNat) -> Type
Solve (Over v f) n = (Subset (LVect v QNat) (\x => (Eval' f x === n)))
||| That `f` is a less general form that `g`, that is, `g` maps to everything that `f` maps to
public export
0 Unify : Rel Form
Unify f g = (1 x : LVect f.vars QNat) -> (Subset (LVect g.vars QNat) (\y => (Eval' f.form x === Eval' g.form y)))

public export
0 Equiv : Rel Form
Equiv f g = (Unify f g, Unify g f)
  
%hint  
public export
equiv : Unify f g => Unify g f => Equiv f g
equiv @{uf} @{ug} = (uf, ug)

