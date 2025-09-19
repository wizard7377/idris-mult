module Data.Mu.Notation 

import Data.Linear.Notation
import Data.Mu.Types 

public export
infixl 1 ^
  
%inline %tcinline
public export
(^) : (t : Type) -> (0 n : Nat) -> Type
(^) t n = M n t 
