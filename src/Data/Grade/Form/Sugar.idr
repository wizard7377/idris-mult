module Data.Grade.Form.Sugar 


import Data.Grade.Form.Types
import Data.Grade.Form.Ops
import Relude 
%default total
public export
interface Formula f where 
    constructor MkFormula
    1 formula : f -@ Form

public export
Formula QNat where 
    formula n = FVal n 

public export
Formula Integer where 
    formula n = assert_linear (\n' => FVal (fromInteger n')) n
public export
Formula Form where 
    formula f = f

public export 
{1 n : QNat} -> Formula (Form' n) where 
    formula f = over f

public export 
Formula t => Formula (Form -@ t) where 
    formula f = formula $ f FVar
  
 
export 
infixl 4 |+| 
export
infixl 5 |*|
export
infixl 3 |^|, |-|

public export
(|+|) : Formula f1 => Formula f2 => f1 -@ f2 -@ Form
(|+|) f1 f2 = FAdd (formula f1) (formula f2)
public export
(|*|) : Formula f1 => Formula f2 => f1 -@ f2 -@ Form
(|*|) f1 f2 = FMul (formula f1) (formula f2)
public export
(|^|) : Formula f1 => Formula f2 => f1 -@ f2 -@ Form
(|^|) f1 f2 = FMax (formula f1) (formula f2)
public export
(|-|) : Formula f1 => Formula f2 => f1 -@ f2 -@ Form
(|-|) f1 f2 = FMin (formula f1) (formula f2)

export 
showOp : FOp -> String 
showOp AddOp = "|+|"
showOp MulOp = "|*|"
showOp MaxOp = "|^|"
showOp MinOp = "|-|"
  
