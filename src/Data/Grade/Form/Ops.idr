
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
Eval' : (1 f : Form) -> (1 x : QNat) -> QNat
Eval' FVar x = x
Eval' (FVal n) x = seq x n
Eval' (FApp g f) x = Eval' g (Eval' f x)
Eval' (FAdd f g) x = let 
    1 [x1, x2] = x.clone 2
  in ladd (Eval' f $ x1.val) ((Eval' g) $ x2.val)
Eval' (FMul f g) x = let 
    1 [x1, x2] = x.clone 2
    in lmul (Eval' f $ x1.val) (Eval' g $ x2.val)
Eval' (FMin f g) x = let
    1 [x1, x2] = x.clone 2
  in lmin (Eval' f $ x1.val) (Eval' g $ x2.val)
Eval' (FMax f g) x = let
    1 [x1, x2] = x.clone 2
  in lmax (Eval' f $ x1.val) (Eval' g $ x2.val)
Eval' (FLeft f) x = let 
  (y # z) = pairing x 
  in seq z (Eval' f y)
Eval' (FRight f) x = let 
  (y # z) = pairing x 
  in seq y (Eval' f z)
public export
0 Eval : (1 f : Form) -> (1 x : QNat) -> QNat
Eval FVar x = x
Eval (FVal n) x = n
Eval (FApp g f) x = Eval g (Eval f x)
Eval (FAdd f g) x = ladd (Eval f x) (Eval g x)
Eval (FMul f g) x = lmul (Eval f x) (Eval g x)
Eval (FMin f g) x = lmin (Eval f x) (Eval g x)
Eval (FMax f g) x = lmax (Eval f x) (Eval g x)
Eval (FLeft f) x = let 
  (y # z) = pairing x 
  in Eval f y
Eval (FRight f) x = let 
  (y # z) = pairing x 
  in Eval f z
%hint
export 
0 eval_eq : {f : Form} -> {x : QNat} -> (Eval' f x === Eval f x)
eval_eq {f=f} {x=x} = believe_me () -- TODO: Prove this

||| Solve the formula `f` for the value `n`, ∈
public export
0 Solve : (1 f : Form) -> (1 n : QNat) -> Type
Solve f n = (Subset QNat (\x => (Eval f x === n)))

||| That `f` is a less general form that `g`, that is, `g` maps to everything that `f` maps to
public export
0 Unify : Rel Form
Unify f g = (1 x : QNat) -> (Subset QNat (\y => (Eval f x === Eval g y)))

public export
0 Equiv : Rel Form
Equiv f g = (Unify f g, Unify g f)
  
%hint  
public export
equiv : Unify f g => Unify g f => Equiv f g
equiv @{uf} @{ug} = (uf, ug)


public export
FSplit : (Form -@ Form -@ Form) -@ Form -@ Form -@ Form
FSplit c f g = c (f <.> FLeft) (g <.> FRight)
