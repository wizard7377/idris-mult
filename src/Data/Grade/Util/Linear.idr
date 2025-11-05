module Data.Grade.Util.Linear 

import public Builtin
import public Data.Linear.Notation
import public Data.Linear.Interface
import Data.Linear.Copies
import public Data.Linear.LVect
import Prelude
%default total
  
||| A "clone" type that allows duplicating values linearly.
||| A Clone x contains a value y along with a proof that y is equal to x.
||| This is better than just storing x directly, because it allows us to pattern match out of these (where we would otherwise get a non-linear use of x or unification of pattern variables)
export
data Clone : {t : Type} -> (x : t) -> Type where 
  Cloned : (1 y : t) -> (0 prf : x === y) -> Clone x

public export 
transClone : (y === x) => Clone x -> Clone y
transClone @{prf} (Cloned x p) = Cloned x (rewrite prf in p)

public export
(.val) : forall t. {0 x : t} -> (1 c : Clone {t} x) -> t
(.val) (Cloned y prf) = y

%hint
public export
0 (.prf) : forall t. {0 x : t} -> (c : Clone {t} x) -> (x === c.val)
(.prf) (Cloned y prf) = prf

public export 
clone : forall t. Consumable t => Duplicable t => {n : Nat} -> (1 x : t) -> LVect n (Clone {t} x)
clone {t} {n=Z} x = seq x []
clone {t} {n=(S n')} x = let 
  (x' :: xs) = duplicate x 
  0 prfX : (x === x') = Refl
  0 prfXs : (x === (extract xs)) = believe_me () 
  1 xs' : (LVect n' (Clone {t} ?)) = clone {t} {n=n'} (extract xs)
  in (Cloned x' prfX) :: (rewrite prfXs in xs')

public export
(.clone) : forall t. Consumable t => Duplicable t => (1 x : t) -> (n : Nat) -> LVect n (Clone {t} x)
(.clone) x {n} = clone {n} x

%defaulthint
public export
0 cloneEq : {a : Clone {t} x} -> {b : Clone {t} x} -> a.val === b.val
cloneEq {a} {b} = trans (sym (a.prf)) b.prf

||| Map a function over a Clone
%inline %tcinline
public export
map_clone : forall p. ((1 y : t) -> p y) -@ Clone {t} x -@ p x
map_clone f (Cloned y prf) = rewrite prf in f y

export 
infixl 1 &$
public export
(&$) : forall p. ((1 y : t) -> p y) -@ Clone {t} x -@ p x
(&$) = map_clone
export 
infixl 9 $$

%inline %tcinline
public export
($$) : forall p. ((1 y : t) -> p y) -@ Clone {t} x -@ p x
($$) = map_clone

public export
Consumable t => Consumable (Clone {t} x) where
  consume (Cloned y prf) = consume y

public export
interface Copy a where
  1 copy : {0 b : a -> a -> Type} -> (1 f : (1 x0 : a) -> (1 x1 : a) -> b x0 x1) -> (1 x : a) -> b x x
  0 copy_eq : 
    {b : a -> a -> Type} -> 
    {f : (1 x0 : a) -> (1 x1 : a) -> b x0 x1} -> 
    {x : a} -> 
    (copy f x === f x x)

public export
Copy () where 
    copy f () = f () ()
    copy_eq {b} {f} {x=()} = Refl
export
infixr 0 =@ 
public export
(=@) : Type -> Type -> Type
c =@ t = {auto 1 prf : c} -> t 
 
