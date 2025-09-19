module Data.Mu.Util.Image 
import Prelude
public export
0 Reach : {0 a, b : Type} -> (f : a -> b) -> Type
Reach f = (x : a) -> (y : b ** (f x === y))

%inline %tcinline
public export
Id : a -> a
Id = id

%inline %tcinline
public export
LId : (1 _ : a) -> a
LId x = x
%inline %tcinline
public export
Const : b -> a -> b
Const = const
%inline %tcinline
public export
LConst : (1 _ : b) -> (0 _ : a) -> b
LConst x y = x
 

%hint
public export
reachSelf : {a : Type} -> Reach {a=a} {b=a} Id
reachSelf x = (x ** Refl)

%hint 
public export
reachConst : {a, b : Type} -> (y : b) -> Reach {a=a} {b=b} (Const y)
reachConst y x = (y ** Refl)
