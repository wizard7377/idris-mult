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
    Id = FVar
    public export
    Lit : QNat -@ Form
    Lit n = FVal n

public export 
Reflexive Form Unify where 
  reflexive x = (LEvidence x Refl)
public export
Transitive Form Unify where 
	transitive p0 p1 x = let 
		1 (LSubset.LEvidence y0 prf0) = p0 x
		1 (LSubset.LEvidence z0 prf1) = p1 y0
		in LSubset.LEvidence z0 (rewrite prf0 in prf1)
  
  
{-

THEOREMS ON FORMULAS

-}

 
%hint public export
0 remove_mul : Eval (x * y) n === (lmul (Eval x n) (Eval y n))
remove_mul = Refl
%hint public export
0 remove_add : Eval (x + y) n === (ladd (Eval x n) (Eval y n))
remove_add = Refl
%hint public export
0 remove_min : Eval (FMin x y) n === (lmin (Eval x n) (Eval y n))
remove_min = Refl
%hint public export
0 remove_max : Eval (FMax x y) n === (lmax (Eval x n) (Eval y n))
remove_max = Refl

{-
THEOREMS ON SOLVING FORMULAS
-}
{-
THEOREMS ON UNIFYING FORMULAS
-}
||| Two formulas are unifiable if they are extensionally equal
%hint public export
0 unify_eq : (forall x. Eval f x === Eval g x) => Unify f g
unify_eq @{prf} x = LSubset.LEvidence x (rewrite prf {x=x} in Refl)

||| Everything is less general than a variable
%hint public export 
0 unify_var : {1 f : Form} -> Unify f FVar
unify_var {f=f} x = (LSubset.LEvidence (Eval f x) Refl)
%hint 
public export
0 unify_app : Unify (f <+> g) f
unify_app x = (LSubset.LEvidence (Eval g x) Refl)
 
%hint 
public export
0 solve_both_add : Solve p a =@ Solve q b =@ Solve (FSplit FAdd p q) (a + b)
solve_both_add @{prf1} @{prf2} = let 
  1 v : QNat = (lpower 2 prf1.fst) * (lpower 3 prf2.fst)
  in ?h0
