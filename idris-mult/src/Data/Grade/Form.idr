module Data.Grade.Form  
import public Data.Grade.QNat
import public Data.Grade.List
import Prelude.Num
%inline %tcinline
public export
Form : Type 
Form = QList QNat

public export
interface Formula a where
  constructor MkFormula
  1 formula : a -@ Form

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
