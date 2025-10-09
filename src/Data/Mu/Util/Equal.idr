module Data.Mu.Util.Equal 
import Builtin
%hint
public export 
hetro_to_simpl : {0 a, b, c : Type} -> {0 x : a} -> {0 y : b} -> {auto 0 prfA : a === c} -> {auto 0 prfB : b === c} -> Equal {a=a,b=b} x y -> Equal {a=c,b=c} (rewrite sym prfA in x) (rewrite sym prfB in y)
hetro_to_simpl Refl = Refl

-- Yay this works :)
  
