module Data.Mu.Simple.Wrap

import Prelude.Interfaces
import Data.Linear.Notation
import Builtin
%auto_lazy off 
  
public export
data E : Type -> Type where 
    MkE : (0 x : a) -> E a
public export
data L : Type -> Type where 
    MkL : (1 x : a) -> L a
public export
data W : Type -> Type where 
    MkW : (1 x : a) -> (1 xs : Lazy (W a)) -> W a

public export 
data Usage : Type where 
    Zero : Usage
    One  : Usage
    Omega : Usage

public export 
M : {1 usage : Usage} -> Type -> Type
M {usage=Zero} = E
M {usage=One} = L
M {usage=Omega} = W
export 
eraseE : {a : Type} -> (0 _ : E a) -> E a
eraseE (MkE x) = MkE x
export 
mapE : {a, b : Type} -> (f : a -@ b) -> E a -@ E b
mapE f (MkE x) = MkE (f x)
 
export 
liftMap : (a -@ b) -> a -> b
liftMap f x = f x
export 
mapL : {a, b : Type} -> (f : a -@ b) -> L a -@ L b
mapL f (MkL x) = MkL (f x)
export
mapW : {a, b : Type} -> (f : a -@ b) -> W a -@ W b
mapW f (MkW x xs) = MkW (f x) (Delay (mapW f (Force xs)))
export 
joinE : {a : Type} -> E (E a) -@ E a
joinE (MkE x) = eraseE x
export
joinL : {a : Type} -> L (L a) -@ L a
joinL (MkL (MkL x)) = MkL x

export 
combine' : W a -@ W a -@ W a
combine' (MkW x xs) y = MkW x (Delay (combine' (Force xs) y))
export
joinW : {a : Type} -> W (W a) -@ W a
joinW (MkW x xs) = combine' x (joinW (Force xs))

