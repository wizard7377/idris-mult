module Data.Mu.Lawful.Notation 

import Data.Linear.Notation
import Data.Mu.Lawful.Types 

public export
infixl 1 ^, +>, ~?
  
%inline %tcinline
public export
(^) : (t : Type) -> (0 n : Nat) -> Type
(^) t n = Lawful.M n t 

%inline %tcinline
public export
0 (+>) : (x : a) -> (xs : Lawful.M n a) -> Type
(+>) x xs = Extends x xs
%inline %tcinline
public export
0 (~?) : (xs : Lawful.M m a) -> (ys : Lawful.M n a) -> Type
(~?) xs ys = Like xs ys

