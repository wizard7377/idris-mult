module Data.Grade.Exp
import Relude
import Data.Grade.Form
import Data.Grade.Cat
import Data.Grade.QNat
import Data.Grade.Omega
import Data.Grade.Logic
import Data.Grade.Mu
%default total
%hide Prelude.Num.Neg
public export
Pos : Type -> Type
Pos a = {b : Type} -> (a -@ b) -@ b
public export
Neg : Type -> Type
Neg a = {b : Type} -> a -@ (b -@ b)
export
data Exp : (n : QNat) -> Type -> Type where
    Pow : forall n, t. (0 w : t) -> (1 source : Mu n t w) -> Exp n t
  
export
infix 1 ~?
public export
data (~?) : Exp p t -> Exp q t -> Type where
  MkSim : (w0 === w1 -@ (Pow w0 _) ~? (Pow w1 _))

public export
Yield : {0 n : QNat} -> Exp (Succ n) t -@ t :*: Exp n t
Yield (Pow w source) = let 
    1 (MS y ys) = source 
  in And y (Pow w ys)
  
  
public export
EZ : {0 w : t} -> Exp 0 t 
EZ {w} = Pow w MZ
public export 
mk : (0 w : t) -> (1 source : Mu n t w) -> Exp n t
mk w source = Pow ? source
public export
extract : Exp 1 t -@ t
extract (Pow w source) = Mu.extract source
public export 
0 witness : Exp n t -> t
witness (Pow w _) = w
public export
source : (1 x : Exp n t) -> Mu n t (witness x)
source (Pow _ x) = x
export 
infixl 3 :^:
export 
infixl 4 +++, +:+ 
export 
infixl 5 ***
export 
infixr 2 :/:
export 
infixr 0 ==>
public export
0 (:^:) : Type -> QNat -> Type
t :^: n = Exp n t
public export
(+++) : QNat -@ QNat -@ QNat
(+++) m n = ladd m n
public export
(***) : QNat -@ QNat -@ QNat
(***) m n = lmul m n
%inline public export
(:/:) : Type -> Type -> Type
t :/: u = u -@ t

public export 
One : Type
One = Unit
public export
Non : Type 
Non = Void

||| Map a linear function over an Exp

public export 
map : 
  forall t, u. 
  (t -@ u) -> 
  forall p. 
  (t :^: p) -@ 
  (u :^: p) 
map f (Pow _ x) = Pow _ (Mu.map f x)
public export
app : 
    forall t, u.
    ((t -@ u) :^: p) -@ 
    (t :^: p) -@ 
    (u :^: p)
app (Pow _ f) (Pow _ x) = Pow _ (Mu.app f x)
  
public export
combine : 
  forall t.
  forall m.
  (1 x : t :^: m) -> 
  forall n.
  (1 y : t :^: n) -> 
  (0 prf : x ~? y) => 
  t :^: (m + n)
combine {m} {n} (Pow _ x) (Pow _ y) @{MkSim prf} = let 
  1 x' : Mu n t _ = rewrite prf in y 
  in Pow _ (Mu.combine x x')
public export
split : 
  {1 m : QNat} ->
  (t :^: (m + n)) -@
  (t :^: m) :*: (t :^: n)
split (Pow _ x) = let 
  1 (And y z) : (Mu m t _ :*: Mu n t _) = Mu.split x 
  in And (Pow _ y) (Pow _ z)



extract' : (1 x : Exp m t) -> {auto 0 _ : x = w} -> Mu m t (witness w)
extract' (Pow _ source) @{prf} = rewrite sym prf in source
public export
join : forall t, m, n. (t :^: m) :^: n -@ t :^: (n *** m)
join (Pow _ x) = let
  1 x' : Mu n (Mu m t (Exp.witness _)) ? = Mu.map' extract' x
  1 y = Mu.join x'
  in (Pow _ y)
  
public export
expand : forall t. {1 m, n : QNat} -> (t :^: (n *** m)) -@ (t :^: m) :^: n
expand (Pow _ source) = Pow _ (map (Pow _) $ Mu.expand source)

public export 
react : 
  forall t, u.
  {1 m, n : QNat} ->
  (((t :^: n) -@ u) :^: m) -@ 
  (t :^: (m *** n)) -@ 
  (u :^: m)
react (Pow _ f) x = let 
  1 x' : (t :^: n) :^: m = Exp.expand x
  1 y = Mu.app f $ Exp.source x'
  in Pow _ y
public export
push : forall t, u, n. (t :*: u) :^: n -@ (t :^: n) :*: (u :^: n)
push (Pow _ p) = let 
    1 (And q r) = Mu.push p
  in And (Pow _ q) (Pow _ r)
public export
pull : forall t, u, n. (t :^: n) :*: (u :^: n) -@ (t :*: u) :^: n
pull (And (Pow _ p) (Pow _ q)) = Pow _ (Mu.pull (And p q))
