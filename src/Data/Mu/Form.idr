module Data.Mu.Form
import Data.Linear.Notation
import Data.Linear.LNat
import Data.Mu.Util.Linear
import Data.Linear.Interface
import Data.Mu.LNat
import Prelude.Num
import Builtin
import Prelude.Types
import Data.Linear.LVect
import Data.Mu.Util.LPair
import Prelude
import Control.Relation

||| A formula for an linear natural number, with exactly one variable
||| Can easily be evaluated with 'feval'
public export
data Form : Type where 
    ||| The argument variable
    FVar : Form 
    ||| A constant value
    FVal : LNat -@ Form 
    ||| Map one formula through another one, ie, g(f(x))
    FApp : (1 g : Form) -> (1 f : Form) -> Form
    ||| Add the result of f with the result of g
    FAdd : Form -@ Form -@ Form
    ||| Multiply the result of f with the result of g
    FMul : Form -@ Form -@ Form
    ||| Take the minimum between the result of f and g
    FMin : Form -@ Form -@ Form
    ||| Take the maximum between the result of f and g
    FMax : Form -@ Form -@ Form
    ||| A custom function from LNat to LNat
    FFun : (LNat -@ LNat) -@ Form
  
public export
Eval' : (1 f : Form) -> LNat -@ LNat
Eval' FVar x = x
Eval' (FVal n) x = seq x n
Eval' (FApp g f) x = Eval' g (Eval' f x)
Eval' (FAdd f g) x = let 
    1 [x1, x2] = x.clone 2
  in ladd (Eval' f $ x1.val) ((Eval' g) $ x2.val)
Eval' (FMul f g) x = let 
    1 [x1, x2] = x.clone 2
    in lmul (Eval' f $ x1.val) (Eval' g $ x2.val)
Eval' (FMin f g) x = let
    1 [x1, x2] = x.clone 2
  in lmin (Eval' f $ x1.val) (Eval' g $ x2.val)
Eval' (FMax f g) x = let
    1 [x1, x2] = x.clone 2
  in lmax (Eval' f $ x1.val) (Eval' g $ x2.val)
Eval' (FFun f) x = f x

public export
0 Eval : (1 f : Form) -> LNat -@ LNat
Eval FVar x = x
Eval (FVal n) x = n
Eval (FApp g f) x = Eval g (Eval f x)
Eval (FAdd f g) x = ladd (Eval f x) (Eval g x)
Eval (FMul f g) x = lmul (Eval f x) (Eval g x)
Eval (FMin f g) x = lmin (Eval f x) (Eval g x)
Eval (FMax f g) x = lmax (Eval f x) (Eval g x)
Eval (FFun f) x = f x

%hint
export 
0 eval_eq : {f : Form} -> {x : LNat} -> (Eval' f x === Eval f x)
eval_eq = ?heval_eq
||| No, this is not a haskell fmap, rather describes a *formula* map :|
public export
fmap : (1 p : LNat -@ LNat) -> (1 f : Form) -> Form
fmap p f = FApp (FFun p) f

public export
0 Solve : (1 f : Form) -> (1 n : LNat) -> Type
Solve f n = (LSubset (\x => (Eval f x === n)))

||| That `f` is a less general form that `g`, that is, `g` maps to everything that `f` maps to
public export
0 Unify : Rel Form
Unify f g = (1 x : LNat) -> (LSubset (\y => (Eval f x === Eval g y)))

namespace Form 
    public export
    Id : Form
    Id = FVar
    public export
    Lit : LNat -@ Form
    Lit n = FVal n

public export 
Reflexive Form Unify where 
  reflexive x = (LEvidence x Refl)
public export
Transitive Form Unify where 
  transitive p0 p1 x = ?h2
  
  
{-

THEOREMS ON FORMULAS

-}

%hint export
0 unify_app : Unify (FApp f g) f
unify_app x = (LSubset.LEvidence (Eval g x) Refl)
  
%hint public export
0 remove_mul : Eval (FMul x y) n === (lmul (Eval x n) (Eval y n))
remove_mul = Refl
%hint public export
0 remove_add : Eval (FAdd x y) n === (ladd (Eval x n) (Eval y n))
remove_add = Refl
%hint public export
0 remove_min : Eval (FMin x y) n === (lmin (Eval x n) (Eval y n))
remove_min = Refl
%hint public export
0 remove_max : Eval (FMax x y) n === (lmax (Eval x n) (Eval y n))

%hint public export
0 unify_eq : (forall x. Eval f x === Eval g x) => Unify f g
unify_eq @{prf} x = LSubset.LEvidence x (rewrite prf {x=x} in Refl)
