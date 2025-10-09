module Data.Mu.Util.LPair
import Builtin
import Prelude.Basics
import Data.Linear.Notation
import Data.Mu.Util.Types
import Prelude.Types
import Prelude.Logic
%hide Basics.(.)

%inline %tcinline
public export 
Pred : (ty : Type) -> Type 
Pred ty = ty -> Type
||| A linear existential type $∃ (x : ty). f x$
||| @ ty in the existential
||| @ f the predicate that must be satisfied, and the type of the value 
public export
record LExists {ty : Type} (f : (ty -> Type)) where
    constructor LEvidence
    ||| A certain `x`
    0 fst : ty 
    ||| A value of `f x`
    1 snd : f fst
  
||| A set (or partion) of values of type `ty` satisfying the predicate `pred`
||| Very much like a refinement type 
||| NOTE: An element of this set is an element of the subset, not the set itself
||| @ ty The type of values in the super set
||| @ pred The predicate that values in the set must satisfy
public export 
record LPart (ty : Type) {pred : ty -> Type} where 
  ||| An element of the set
  constructor LElement 
  ||| The value in the set
  1 val : ty 
  ||| The proof that the value satisfies the predicate
  0 prf : (pred val)


%inline %tcinline public export
0 prfExists : (e : LExists {ty} _) -> ty  
prfExists {e=LEvidence p v} = p
%inline %tcinline public export
valExists : (1 e : LExists {ty} f) -> f (prfExists e)
valExists {e=LEvidence p v} = v
%inline %tcinline public export
valPart : (1 s : LPart ty {pred}) -> ty
valPart {s=LElement v p} = v
%inline %tcinline public export
0 prfPart : (s : LPart ty {pred}) -> (pred (valPart s))
prfPart {s=LElement v p} = p
%inline %tcinline public export
TruePred : {0 a : Type} -> Pred a
TruePred = Const ()
%inline %tcinline public export
TruePart : (ty : Type) -> Type
TruePart ty = LPart ty {pred=TruePred}

public export
mapPart : 
    forall a, p, q.
    (1 f : a -@ a) -> 
    (1 ex : LPart a {pred=p}) ->
    {auto 0 prf : forall y. (p y) -> (q (f y))} -> 
    LPart a {pred=q}
mapPart f (LElement x px) @{prf} = LElement (f x) (prf px)

public export
mapExists : 
  forall a, b, p, q. 
    {0 f : a -> b} -> 
    (1 g : ({0 x : a} -> p x -@ q (f x))) ->
    (1 ex : LExists {ty=a} p) ->
    LExists {ty=b} q
mapExists {f} g (LEvidence x y) = LEvidence (f x) (g y)


public export
dimapExists : 
  forall a, b, p, q. 
    {0 f : a -> b} -> 
    (1 g : ({0 x : a} -> p x -@ q (f x))) ->
    (1 ex : LExists {ty=a} p) ->
    LExists {ty=b} q
dimapExists {f} g (LEvidence x y) = LEvidence (f x) (g y)


export 
infixr 9 *:, :*, *:* 
export 
infixr 0 $*, *$, *$*
export 
infixl 1 *+, +*, *+*

