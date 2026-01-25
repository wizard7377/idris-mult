module Data.Grade.Logic
import Builtin
import Data.Linear.Notation
import Prelude.Linear
import Prelude.Copy
import Prelude.Clone
import Prelude.Types
||| Contractible types 
public export
record Contractible (0 a : Type) where 
    constructor Contract
    1 center' : a
    0 deform : {x : a} -> (x = center')

public export
contract : {0 a : Type} -> (1 x : a) => (0 prf : {0 y : a} -> (y === x) ) => Contractible a
contract @{x} @{prf} = Contract x prf
public export
(.center) : Contractible a -@ a
(.center) (Contract c d) = c

public export
Point : (1 _ : Contractible a) => a
Point @{c} = c.center

public export
data QDec : Type -> Type where
    QYes : a -@ QDec a
    QNo : (a -@ Void) -@ QDec a

public export
interface QDecEq (0 t : Type) where 
  %hint
  1 qDecEq : {1 x, y : t} -> QDec (x === y)

public export
QNot : (t : Type) -> Type
QNot t = (t -@ Void)

public export
MkNot : QNot t -@ (t -> Void)
MkNot f x = f x
public export
efalse : forall t. (0 prf : Void) -> t
efalse prf impossible 
  
||| From erased equality to unrestricted equality, using UIP 
||| Called a scandel because it makes things relevant ;)
public export
scandel : (0 prf : x = y) -> (x = y)
scandel prf = rewrite prf in Refl

public export
decScandel : (0 prf : Dec (x = y)) -> Dec (x === y)
decScandel = believe_me ()
export
infixr 2 |*|
export 
infixr 2 |+|
export
infixl 4 :+:
export
infixl 5 :*:

||| consume both, ⊗ per Girard
public export
data (:*:) : Type -> Type -> Type where
  And : forall a, b. a -@ b -@ (a :*: b)
  
||| Use one, consume one, ⊕ per Girard
public export
data (|+|) : Type -> Type -> Type where
  InL : forall a, b. a -@ (a |+| b)
  InR : forall a, b. b -@ (a |+| b)
||| Provide either, consume either, & per Girard
public export
data (:+:) : Type -> Type -> Type where
  Par : (forall r. ((a -@ r) |+| (b -@ r)) -@ r) -@ (a :+: b)
  
||| Provide one, consume both , ⅋ per Girard
public export
data (|*|) : Type -> Type -> Type where
  Rap : (forall r. ((a :*: b) -@ r) -@ r) -@ (a |*| b)

export
infix 1 =? 
%inline %tcinline 
public export
(=?) : Type -> Type -> Type
a =? b = Equal a b

namespace Par
    public export 
    (.fst) : (a :+: b) -@ a
    (.fst) (Par f) = f (InL $ \x => x)
    public export
    (.snd) : (a :+: b) -@ b
    (.snd) (Par f) = f (InR $ \x => x)

    public export 
    get_left : (a :+: b) -@ a
    get_left p = p.fst
    public export
    get_right : (a :+: b) -@ b
    get_right p = p.snd

    private 
    LinComp : (b -@ c) -@ (a -@ b) -@ (a -@ c)
    LinComp f g = \x => f (g x)
    public export
    map : ((a -@ a') :+: (b -@ b')) -@ (a :+: b) -@ (a' :+: b')
    map (Par f) (Par p) = Par $ \x => case x of
        InL y => p (InL $ f $ InL $ LinComp y)
        InR y => p (InR $ f $ InR $ LinComp y)

    ||| Girard's `?` modality, which models a value that might exist
    public export
    Quest : Type -> Type
    Quest a = a :+: ()

    public export
    use_quest : Quest a -@ a
    use_quest (Par f) = f (InL $ \x => x)

    public export
    mk : (c -@ a) => (c -@ b) => c -@ (a :+: b)
    mk @{f} @{g} x = Par $ \h => case h of
        InL p => p (f x)
        InR q => q (g x)
    public export 
    viewPar : a -@ ((a -@ b) :+: (a -@ c)) -@ (b :+: c)
    viewPar x f = Par $ \g => case g of
        InL h => h $ (get_left f) x
        InR h => h $ (get_right f) x 

    public export 
    swap : a :+: b -@ b :+: a
    swap (Par f) = Par $ \g => case g of
        InL h => f (InR h)
        InR h => f (InL h)
    public export 
    remove_rhs : a :+: Void -@ a 
    remove_rhs (Par f) = f (InL $ \x => x)
    public export
    Drop (Quest a) where
        drop (Par f) = f (InR $ \() => ())
namespace And 
  public export
  fst : (a :*: b) -> a
  fst (And x y) = x
  public export
  snd : (a :*: b) -> b
  snd (And x y) = y




namespace Lemma
