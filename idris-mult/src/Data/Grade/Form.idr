module Data.Grade.Form  
import public Data.Grade.QNat
import public Data.Grade.List
import Prelude.Num
import Data.Grade.Sigma
import Data.Grade.Logic
%inline %tcinline
public export
Form : Type 
Form = QList QNat
public export
Solve : Form -> Type
Solve l = Subset QNat (\n => IsElem n l)

%inline %tcinline
public export
(.val) : Solve l -@ QNat
(.val) (Elem v prf) = v
public export
interface Formula a where
  constructor MkFormula
  1 formula : a -@ Form
public export
Drop (Solve l) where
  drop (Elem x prf) = drop x

public export
Copy (Solve l) where
  copy x f = ?copy_solve
export 
infixl 5 |+|
export 
infixl 4 |*|
public export
(|+|) : Formula a => Formula b => a -@ b -@ Form
(|+|) @{ (MkFormula f) } @{ (MkFormula g) } x y = App2 ladd (f x) (g y)
public export
(|*|) : Formula a => Formula b => a -@ b -@ Form
(|*|) @{ (MkFormula f) } @{ (MkFormula g) } x y = App2 lmul (f x) (g y)
public export
Formula Integer where
  formula x = [assert_linear fromInteger x]
public export
Formula QNat where
  formula x = [x]
public export
Formula (QList QNat) where
  formula x = x
public export
SolveFun : {0 f : QNat -@ QNat -@ QNat} -> (1 s : Solve (App2 f p q)) => Subset (Solve p *** Solve q) (\ (And s_p s_q) => f s_p.val s_q.val === s.val)
SolveFun {f} @{(Elem s_val s_prf)} = Elem (And (Elem ?s_p_n ?s_p_prf) (Elem ?s_q_n ?s_q_prf)) ?solve_fun_rhs
