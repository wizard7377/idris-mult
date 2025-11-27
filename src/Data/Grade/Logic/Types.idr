module Data.Grade.Logic.Types
import Builtin
import Prelude.Basics
import Data.Linear.Notation
import Data.Grade.Util.Types
import Data.Linear.Interface
import Prelude.Types
 
||| A linear existential type $∃ (x : ty). f x$
||| @ ty in the existential
||| @ f the predicate that must be satisfied, and the type of the value 
public export
record Exists (t : Type) (p : (t -> Type)) where
    constructor Given
    ||| A certain `x`
    0 fst' : t 
    ||| A value of `f x`
    1 snd' : p fst'

public export
exists : {0 t : Type} -> {0 p : (t -> Type)} -> {0 x : t} -> (1 y : p x) -> Exists t p
exists {t} {p} {x} y = Given x y
||| A linear existential type $∃ (x : ty). f x$
||| @ ty in the existential
||| @ f the predicate that must be satisfied, and the type of the value 
public export
record Subset (t : Type) (p : (t -> Type)) where
    constructor Elem
    ||| A certain `x`
    1 fst' : t 
    ||| A value of `f x`
    0 snd' : p fst'

||| A linear existential type $∃ (x : ty). f x$
||| @ ty in the existential
||| @ f the predicate that must be satisfied, and the type of the value 
public export
record Sigma (t : Type) (p : (t -> Type)) where
    constructor For
    ||| A certain `x`
    1 fst' : t 
    ||| A value of `f x`
    1 snd' : p fst'
public export
data Erase : Type -> Type where
    MkErase : (0 x : t) -> Erase t
public export
0 Forall : (t : Type) -> (p : (t -> Type)) -> Type
Forall t p = {0 x : t} -> p x
export typebind infixr 0 #?

%inline %tcinline
public export
0 (#?) : (t : Type) -> (p : (t -> Type)) -> Type
(#?) t p = Exists t p

export infixl 9 #*

%inline %tcinline
public export
(#*) : (fst : t) -> (snd : f fst) -> (Exists t f)
(#*) x y = Given x y
%hide Basics.(.)

public export
Duple : Type -> Type -> Type
Duple a b = Sigma a (\_ => b)
namespace Exists
    
    %inline %tcinline 
    public export
    0 (.fst) : (ex : Exists ty f) -> ty
    (.fst) (Given x y) = x
    %inline %tcinline 
    public export
    (.snd) : (1 ex : Exists ty f) -> f (ex.fst)
    (.snd) (Given x y) = y
    %inline %tcinline 
    public export
    0 fst : (ex : Exists ty f) -> ty
    fst = (.fst)
    %inline %tcinline 
    public export
    snd : (1 ex : Exists ty f) -> f (ex.fst)
    snd = (.snd)
    public export 
    map : 
    {0 p : a -> Type} -> 
    {0 q : b -> Type} -> 
    {0 m : (a -> b)} -> 
    (1 f : forall x. p x -@ q (m x)) -> 
    (Exists a p -@ Exists b q)
    map f (Given x y) = Given (m x) (f y)

    public export
    mapSnd : {0 p : a -> Type} -> {0 q : (a -> Type)} -> (1 f : forall x. p x -@ q x) -> (Exists a p -@ Exists a q)
    mapSnd f (Given x y) = Given x (f y)
    public export
    compose : 
        {0 p : a -> Type} -> 
        {0 q : b -> Type} -> 
        {0 r : c -> Type} -> 
        {0 m : (a -> b)} -> 
        {0 n : (b -> c)} -> 
        (1 f : forall x. p x -@ q (m x)) -> 
        (1 g : forall y. q y -@ r (n y)) ->
        (Exists a p -@ Exists c r)
    compose f g (Given x y) = Given (n (m x)) (g (f y))
    
namespace Subset
    
    %inline %tcinline 
    public export
    (.fst) : (1 ex : Subset ty f) -> ty
    (.fst) (Elem x y) = x
    %inline %tcinline 
    public export
    0 (.snd) : (1 ex : Subset ty f) -> f (ex.fst)
    (.snd) (Elem x y) = y
    %inline %tcinline 
    public export
    fst : (1 ex : Subset ty f) -> ty
    fst = (.fst)
    %inline %tcinline 
    public export
    0 snd : (1 ex : Subset ty f) -> f (ex.fst)
    snd = (.snd)
    public export 
    map : 
    {0 p : a -> Type} -> 
    {0 q : b -> Type} -> 
    (1 m : (a -@ b)) -> 
    {0 f : forall x. p x -> q (m x)} -> 
    (Subset a p -@ Subset b q)
    map m {f} (Elem x y) = Elem (m x) (f y)

    public export
    mapSnd : {0 p : a -> Type} -> {0 q : (a -> Type)} -> (0 f : forall x. p x -@ q x) -> (Subset a p -@ Subset a q)
    mapSnd f (Elem x y) = Elem x (f y)
    public export
    compose : 
        {0 p : a -> Type} -> 
        {0 q : b -> Type} -> 
        {0 r : c -> Type} -> 
        (1 m : (a -@ b)) -> 
        (1 n : (b -@ c)) -> 
        {0 f : forall x. p x -@ q (m x)} -> 
        {0 g : forall y. q y -@ r (n y)} ->
        (Subset a p -@ Subset c r)
    compose m n {f} {g} (Elem x y) = Elem (n (m x)) (g (f y))
    
public export
NegationExists : Not (Exists t p) -> {w : t} -> Not (p w)
NegationExists notEx {w} prf = 
    let ex : Exists t p
        ex = Given w prf
    in notEx ex
public export
ExistsNegation : Forall t (\x => Not (p x)) -> Not (Exists t p)
ExistsNegation allNot (Given x prf) = allNot {x} prf

namespace Sigma
    
    %inline %tcinline 
    public export
    0 (.fst) : (Sigma ty f) -@ ty
    (.fst) (For x y) = x
    %inline %tcinline 
    public export
    0 (.snd) : (1 ex : Sigma ty f) -> f (ex.fst)
    (.snd) (For x y) = y
    %inline %tcinline 
    public export
    0 fst : (1 ex : Sigma ty f) -> ty
    fst = (.fst)
    %inline %tcinline 
    public export
    0 snd : (1 ex : Sigma ty f) -> f (ex.fst)
    snd = (.snd)
    public export 
    map : 
    {0 p : a -> Type} -> 
    {0 q : b -> Type} -> 
    {1 m : (a -@ b)} -> 
    (1 f : forall x. p x -@ q (m x)) -> 
    (Sigma a p -@ Sigma b q)
    map f (For x y) = For (m x) (f y)

    public export
    mapSnd : {0 p : a -> Type} -> {0 q : (a -> Type)} -> (1 f : forall x. p x -@ q x) -> (Sigma a p -@ Sigma a q)
    mapSnd f (For x y) = For x (f y)
    public export
    compose : 
        {0 p : a -> Type} -> 
        {0 q : b -> Type} -> 
        {0 r : c -> Type} -> 
        {1 m : (a -@ b)} -> 
        {1 n : (b -@ c)} -> 
        (1 f : forall x. p x -@ q (m x)) -> 
        (1 g : forall y. q y -@ r (n y)) ->
        (Sigma a p -@ Sigma c r)
    compose f g (For x y) = For (n (m x)) (g (f y))
 
