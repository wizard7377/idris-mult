module Data.Grade.Hott 
import Relude
%hide Prelude.Ops.infix.(<=>)
%hide Prelude.Types.(<=>)
public export
Id : {0 a : Type} -> a -@ a
Id x = x
export 
infixr 9 <.>
public export
(<.>) : (b -@ c) -@ (a -@ b)-@ (a -@ c)
(<.>) g f = \x => g $ f $ x
export
infix 2 ==>, <==, <=>, <~>
public export 
0 Fam : Type -> Type
Fam a = a -> Type
public export
0 Pi : (a : Type) -> (p : Fam a) -> Type 
Pi a p = (1 x : a) -> p x 
public export
data (<~>) : {0 b : Fam a} -> (f : Pi a b) -> (g : Pi a b) -> Type where 
  Identity : {0 f : a -@ b} -> {0 g : a -@ b} -> ((0 x : a) -> f x = g x) -@ f <~> g

-- A > B, or
public export
record LInv (f : a -@ b) where 
  constructor MkLInv 
  1 g : b -@ a 
  0 prf : (g <.> f) <~> Id

-- A < B
public export
record RInv (f : a -@ b) where
  constructor MkRInv 
  1 g : b -@ a 
  0 prf : (f <.> g) <~> Id
  
  
public export
data (==>) : Type -> Type -> Type where
  IsLInv : (f : a -@ b) ->? LInv f -@ (a ==> b)
public export
data (<==) : Type -> Type -> Type where
  IsRInv : (f : a -@ b) ->? RInv f -@ (a <== b)
public export
data (<=>) : Type -> Type -> Type where
  IsEquiv : (f : a -@ b) ->? LInv f =@ RInv f =@ (a <=> b)
%hint export
mk_LInv : 
  {0 a, b : Type} -> 
  (0 f : a -@ b) -> 
  (1 g : b -@ a) => 
  (0 prf : (g <.> f) <~> Id) => 
  LInv f
mk_LInv {a, b} f {g, prf} = MkLInv g prf
%hint export
mk_RInv : 
  {0 a, b : Type} -> 
  (0 f : a -@ b) -> 
  (1 g : b -@ a) => 
  (0 prf : (f <.> g) <~> Id) => RInv f
mk_RInv {a, b} f {g, prf} = MkRInv g prf


namespace Homotopy
    %hint export
    mk : (0 f : a -@ b) -> (0 g : a -@ b) -> (1 prf : (0 x : a) -> f x = g x) => f <~> g 
    mk f g @{prf} = Identity prf
    
    export 
    (.ap) : 
        {0 f, g : a -@ b} ->
        (1 p : f <~> g) ->  
        (0 x : a) -> 
        f x = g x
    (.ap) p x = case p of 
        Identity prf => prf x
    %hint export
    refl' : (0 f : a -@ a) -> f <~> f
    refl' f = Homotopy.mk f f @{ %search }
    
    %hint export
    refl : (0 f, g : a -@ a) -> ((0 prf : f === g) => f <~> g)
    refl f g @{prf} = rewrite prf in refl' g

    %hint export 
    sym : (0 f : a -@ b) -> (0 g : a -@ b) -> f <~> g =@ g <~> f
    sym f g @{ Identity prf } = Homotopy.mk g f @{ \x => (prf x >>> sym (prf x)) }

    %hint export 
    trans : (0 f : a -@ b) -> (0 g : a -@ b) -> (0 h : a -@ b) -> f <~> g =@ g <~> h =@ f <~> h
    trans f g h @{ Identity prf1 } @{ Identity prf2 } = Homotopy.mk f h @{ \x => prf1 x >>> prf2 x >>> trans (prf1 x) (prf2 x) }
    %hint export
    join : 
      forall a, b, c. 
      (0 f, f' : a -@ b) -> 
      (0 g, g' : b -@ c) -> 
      (
      (0 p : f <~> f') => 
      (0 q : g <~> g') => 
      ((g <.> f) <~> (g' <.> f'))
      )
    join f f' g g' @{ Identity p } @{ Identity q } = Identity (\x => rewrite (p x) in rewrite q (f' x) in Refl) 
    
namespace Inv 
    namespace Left
        %hint export
        mk : 
            forall a, b.
            (0 f : a -@ b) -> 
            (1 g : b -@ a) -> 
            (0 prf : (g <.> f) <~> Id) =>
            a ==> b
        mk {a, b} f g {prf} = IsLInv f (MkLInv g prf) 
        %hint export 
        refl : forall a. a ==> a
        refl {a} = mk Id Id
    namespace Right
        %hint export
        mk : 
            forall a, b.
            (0 f : a -@ b) -> 
            (1 g : b -@ a) -> 
            (0 prf : (f <.> g) <~> Id) =>
            a <== b
        mk {a, b} f g {prf} = IsRInv f (MkRInv g prf) 
        %hint export 
        refl : forall a. a <== a
        refl {a} = mk Id Id 
    
