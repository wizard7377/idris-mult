module Data.Grade.Util.LPair
import Builtin
import Prelude.Basics
import Data.Linear.Notation
import Data.Grade.Util.Types
import Prelude.Types
 
||| A linear existential type $∃ (x : ty). f x$
||| @ ty in the existential
||| @ f the predicate that must be satisfied, and the type of the value 
public export
record Exists (t : Type) (p : (t -> Type)) where
    constructor Evidence
    ||| A certain `x`
    0 fst' : t 
    ||| A value of `f x`
    1 snd' : p fst'

public export
exists : {0 t : Type} -> {0 p : (t -> Type)} -> {0 x : t} -> (1 y : p x) -> Exists t p
exists {t} {p} {x} y = Evidence x y
||| A linear existential type $∃ (x : ty). f x$
||| @ ty in the existential
||| @ f the predicate that must be satisfied, and the type of the value 
public export
record Subset (t : Type) (p : (t -> Type)) where
    constructor Element
    ||| A certain `x`
    1 fst' : t 
    ||| A value of `f x`
    0 snd' : p fst'


export typebind infixr 0 #?

%inline %tcinline
public export
0 (#?) : (t : Type) -> (p : (t -> Type)) -> Type
(#?) t p = Exists t p

export infixl 9 #*

%inline %tcinline
public export
(#*) : (fst : t) -> (snd : f fst) -> (Exists t f)
(#*) x y = Evidence x y
%hide Basics.(.)
namespace Exists
    
    %inline %tcinline 
    public export
    0 (.fst) : (ex : Exists ty f) -> ty
    (.fst) (Evidence x y) = x
    %inline %tcinline 
    public export
    (.snd) : (1 ex : Exists ty f) -> f (ex.fst)
    (.snd) (Evidence x y) = y
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
    map f (Evidence x y) = Evidence (m x) (f y)

    public export
    mapSnd : {0 p : a -> Type} -> {0 q : (a -> Type)} -> (1 f : forall x. p x -@ q x) -> (Exists a p -@ Exists a q)
    mapSnd f (Evidence x y) = Evidence x (f y)
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
    compose f g (Evidence x y) = Evidence (n (m x)) (g (f y))
    
namespace Subset
    
    %inline %tcinline 
    public export
    (.fst) : (1 ex : Subset ty f) -> ty
    (.fst) (Element x y) = x
    %inline %tcinline 
    public export
    0 (.snd) : (1 ex : Subset ty f) -> f (ex.fst)
    (.snd) (Element x y) = y
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
    map m {f} (Element x y) = Element (m x) (f y)

    public export
    mapSnd : {0 p : a -> Type} -> {0 q : (a -> Type)} -> (0 f : forall x. p x -@ q x) -> (Subset a p -@ Subset a q)
    mapSnd f (Element x y) = Element x (f y)
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
    compose m n {f} {g} (Element x y) = Element (n (m x)) (g (f y))
    
