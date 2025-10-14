module Data.Mu.Util.Equal 
import Builtin
export 
infixr 6 =?

public export 
(=?) : (x : a) -> (y : a) -> Type
(=?) x y = Equal x y
public export 
hetro_to_simpl : {0 a, b, c : Type} -> {0 x : a} -> {0 y : b} -> {auto 0 prfA : a === c} -> {auto 0 prfB : b === c} -> Equal {a=a,b=b} x y -> Equal {a=c,b=c} (rewrite sym prfA in x) (rewrite sym prfB in y)
hetro_to_simpl Refl = Refl

public export
hetro_to_simpl_same : {0 a : Type} -> {0 b : Type} -> {0 x : a} -> {0 y : b} -> {auto 0 prfA : a === b} -> Equal {a=a,b=b} x y -> Equal {a=b,b=b} (rewrite sym prfA in x) y
hetro_to_simpl_same Refl = Refl
-- Yay this works :)
  
