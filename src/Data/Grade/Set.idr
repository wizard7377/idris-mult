module Data.Grade.Set

import Data.Grade.Util.Relude 
import Prelude.Uninhabited
import public Data.Grade.Logic

||| A set over some type, that is, `Set ty` is a predicate over `ty`
%inline %tcinline
public export
0 Set : (a : Type) -> Type 
Set a = (1 x : a) -> Type

public export
infixl 1 <:

%inline %tcinline
public export
0 (<:) : (x : a) -> Set a -> Type
x <: a = a x


public export
0 EmptySet : Set a
EmptySet x = Void
public export
0 UniversalSet : Set a
UniversalSet x = Unit
public export
0 Union : Set a -> Set a -> Set a 
Union p q = \x => Either (x <: p) (x <: q)
public export
0 Intersect : Set a -> Set a -> Set a
Intersect p q = \x => (x <: p , x <: q)
public export
0 Power : Set a -> Set (Set a)
Power p = \q => (forall x. (x <: q) -> (x <: p))

public export
infixr 0 ->? 
%inline %tcinline
public export
0 (->?) : Set a -> Set a -> Type
p ->? q = q <: (Power p)

||| Intuitively, the set of all things that "were" a given value before some function was applied
public export
0 WasSet : (a -> a) -> Set a -> Set a
WasSet f p = \x => (y : a ** (x = f y , y <: p))
public export
0 ExSet : (p : a -> Set b) -> Set b
ExSet p = \x => (y : a ** (x <: p y))

public export
0 EqSet : (x : a) -> Set a
EqSet x = \y => (x = y)

public export
0 MapSet : (f : a -> b) -> Set b -> Set a
MapSet f p = \x => f x <: p

public export
0 Multiple : (n : QNat) -> Set QNat
Multiple n = ExSet (\k => EqSet (n * k))
