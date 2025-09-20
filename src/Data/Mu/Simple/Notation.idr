module Data.Mu.Simple.Notation 

import Data.Linear.Notation
import Data.Mu.Simple.Types 

public export
infixl 1 ^, +>, ~?
  
%inline %tcinline
public export
(^) : (t : Type) -> (0 n : Nat) -> Type
(^) t n = M n t 

%inline %tcinline
public export
0 (+>) : (x : a) -> (xs : M n a) -> Type
(+>) x xs = Extends x xs
%inline %tcinline
public export
0 (~?) : (xs : M m a) -> (ys : M n a) -> Type
(~?) xs ys = Like xs ys
