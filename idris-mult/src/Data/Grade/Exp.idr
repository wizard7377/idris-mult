module Data.Grade.Exp
import Relude
import Data.Grade.Form
import Data.Grade.Omega
import Data.Grade.QNat
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
%noinline
public export
0 Exp : (p : Form) -> Type -> Type
Exp p t = Exists t (Omega p t)
export 
infixl 3 ^, ^-, ^+, -^, +^
public export
0 (^) : Type -> (p : Form) -> Type
(^) t p = Exp p t

public export
0 (^-) : Type -> (p : Form) -> Type
(^-) t p = Neg (Exp p t)

public export
0 (^+) : Type -> (p : Form) -> Type
(^+) t p = Pos (Exp p t)

public export
0 (-^) : Type -> (p : Form) -> Type
(-^) t p = Exp p (Neg t)
public export
0 (+^) : Type -> (p : Form) -> Type
(+^) t p = Exp p (Pos t)

||| Map a linear function over an Exp
public export
map : {0 r : t -@ u} -> (forall w. Omega p t w -@ Omega q u (r w)) -@ (t ^ p) -@ (u ^ q)
map f (Given n x) = (Given (r n) (f x))
public export
box : Omega p t w -@ (t ^ p)
box {w} x = Given w x
public export
unbox : (1 x : t ^ p) -> Omega p t x.fst
unbox (Given n x) = x
public export
gen : {p : Form} -> (!* t) -@ (t ^ p) 
gen (MkBang x) = ?gen_rhs -- Given x (gen (MkBang x))
public export
combine : {0 m, n : Form} -> (1 x : t ^ m) -> (1 y : t ^ n) -> (x.fst = y.fst) |- (t ^ (m |+| n))
combine (Given w x) (Given _ y) @{ Refl } = Given w (Omega.combine x y)
public export
join : {0 m, n : Form} -> ((t ^ n) ^ m) -@ (t ^ (m |*| n)) 

public export
split : (t ^ (m |*| n)) -@ ((t ^ m) `Duple` (t ^ n))
public export
expand : (t ^ (m |*| n)) -@ (t ^ m ^ n)

