module Data.Grade.Form.Types
import Data.Linear.Notation
import Data.Grade.Util.Linear
import Data.Nat
import Data.Linear.Interface
import Data.Grade.QNat
import Prelude.Num
import Builtin
import Prelude.Types
import Data.Linear.LVect
import Data.Linear.LMaybe
import Data.Grade.Logic
import Prelude
import Control.Relation
import Relude


||| A vector with a linear natural number length
public export
data QVect : QNat -> Type -> Type where 
    Nil : QVect 0 a
    (::) : (1 x : a) -> (1 xs : QVect n a) -> QVect (Succ n) a

||| Append an element to the end of a linear vector
public export
snoc : {1 n : QNat} -> (1 xs : QVect n a) -> (1 x : a) -> QVect (Succ n) a
snoc Nil x = x :: Nil
snoc (y :: ys) x = y :: snoc ys x
||| Append two linear vectors 
public export
append : QVect m a -> QVect n a -> QVect (m + n) a
append Nil ys = ys
append (x :: xs) ys = x :: append xs ys
||| Split a linear vector at a given position
public export
splitAt : (1 m : QNat) -> (1 xs : QVect (m + n) a) -> LPair (QVect m a) (QVect n a)
splitAt Zero xs = Nil # xs
splitAt (Succ m') (x :: xs) = let 
  1 r = splitAt m' xs
  (y # z) = r
  in (x :: y) # z
public export  
data FOp = AddOp | MulOp | MaxOp | MinOp

public export
Consumable FOp where 
    consume AddOp = ()
    consume MulOp = ()
    consume MaxOp = ()
    consume MinOp = ()
public export 
runOp : FOp -@ QNat -@ QNat -@ QNat
runOp AddOp = ladd 
runOp MulOp = lmul
runOp MaxOp = lmax
runOp MinOp = lmin
||| A formula for an linear natural number, with exactly one variable
||| Can easily be evaluated with 'feval'
public export
data Form' : QNat -> Type where 
    ||| The argument variable
    FVar' : Form' 1
    ||| A constant value
    FVal' : (1 n : QNat) -> Form' 0
    FApp' : (1 op : FOp) -> {1 a : QNat} -> (1 x : Form' a) -> (1 y : Form' b) -> Form' (a + b)
%name Form' φ, ψ    

public export
Consumable (Form' n) where 
  consume f = assert_total $ case f of 
    FVar' => ()
    FVal' n => consume n
    FApp' {a} op x y => seq a $ seq x $ seq y $ consume op

public export 
Copy (Form' n) where 
  copy f x = assert_total $ case x of 
    FVar' => f FVar' FVar'
    FVal' n => copy (\a, b => f (FVal' a) (FVal' b)) n
    FApp' {a} op x y => ?fa
  copy_eq = ?ce
export 
infixl 4 #+#
export 
infixl 5 #*#
export 
infixr 9 #$#
export 
prefix 9 ###

public export
(#+#) : {1 a : QNat} -> (1 f : Form' a) -> (1 g : Form' b) -> Form' (a + b)
f #+# g = (FApp' AddOp) f g
public export
(#*#) : {1 a : QNat} -> (1 f : Form' a) -> (1 g : Form' b) -> Form' (a + b)
f #*# g = (FApp' MulOp) f g
public export
(###) : QNat -@ Form' 0
(###) n = FVal' n

||| A formula abstracted over a number of variables
public export
record Form where
    constructor Over 
    1 vars : QNat
    1 form : Form' vars
||| Smart constructor for Form 
public export
over : {1 n : QNat} -> Form' n -@ Form
over {n} f = Over n f
public export
(.under) : (1 x : Form) -> Form' x.vars
(.under) (Over n f) = seq n f
 
public export
getVars : (1 f : Form) -> QNat
getVars (Over n g) = seq g n
public export
Num Form where 
    fromInteger n = Over 0 (FVal' (fromInteger n))
    (Over n f) + (Over m g) = Over (n + m) (f #+# g)
    (Over n f) * (Over m g) = Over (n + m) (f #*# g)
 
public export 
FVar : Form 
FVar = over FVar' 
public export
FVal : (1 n : QNat) -> Form
FVal n = over (FVal' n)

public export
FApp : (1 op : FOp) -> (1 f : Form) -> (1 g : Form) -> Form
FApp op (Over n f) (Over m g) = let 
  [n0, n1] = n.clone 2
  1 f' : Form' n1.val := rewrite sym n1.prf in f
  in Over (ladd n0.val m) (rewrite cloneEq {a=n0} {b=n1} in FApp' op f' g)
public export
FAdd : (1 f : Form) -> (1 g : Form) -> Form
FAdd = FApp AddOp
public export
FMul : (1 f : Form) -> (1 g : Form) -> Form
FMul = FApp MulOp
public export
FMax : (1 f : Form) -> (1 g : Form) -> Form
FMax = FApp MaxOp
public export
FMin : (1 f : Form) -> (1 g : Form) -> Form
FMin = FApp MinOp
export
FRange : (1 lo : QNat) -> (1 hi : QNat) -> (1 f : Form) -> Form
FRange lo hi (Over n f) = ?hfr

export
Var : Form 
Var = FVar
public export
Simple : (Form -@ Form) -@ Form 
Simple f = f FVar

public export
VectSplitEq : Exists (QVect (m + n) a) p <=> Exists (QVect m a) (\x => (Exists (QVect n a) (\y => p (append x y))))
VectSplitEq = MkEquivalence fwd bck 
  where 
    fwd : 
       Exists (QVect (m + n) a) p -> 
       Exists (QVect m a) (\x => (Exists (QVect n a) (\y => p (append x y)))) 
    fwd (Given v prf) = ?hf
    bck : 
      (Exists (QVect m a) (\x => (Exists (QVect n a) (\y => p (append x y))))) -> 
      Exists (QVect (m + n) a) p
    bck (Given x (Given y prf)) = Given (append x y) prf
     
  
export 
FAddVars : ((FApp op p q).vars === p.vars + q.vars)
FAddVars {op} {p} {q} = ?fav
%name Form φ, ψ    
