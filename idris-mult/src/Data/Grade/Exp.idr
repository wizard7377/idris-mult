module Data.Grade.Exp
import Relude
import Data.Grade.Form
import Data.Grade.Omega
import Data.Grade.Cat
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
public export
data Exp : (p : Form) -> Type -> Type where
    Pow : (0 w : t) -> (1 source : Omega p t w) -> Exp p t
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
export
infix 1 ~?
public export
0 (~?) : Exp p t -> Exp q t -> Type
(Pow w0 _) ~? (Pow w1 _) = w0 === w1
||| Map a linear function over an Exp
public export
map : {0 r : t -@ u} -> (forall w. Omega p t w -@ Omega q u (r w)) -@ (t ^ p) -@ (u ^ q)
map f (Pow n x) = Pow (r n) (f x)
public export
box : Omega p t w -@ (t ^ p)
box {w} x = Pow w x
public export
gen : {p : Form} -> (!* t) -@ (t ^ p) 
gen (MkBang x) = ?gen_rhs -- Given x (gen (MkBang x))
public export
combine : {0 m, n : Form} -> (1 x : t ^ m) -> (1 y : t ^ n) -> (x ~? y) |- (t ^ (m |+| n))
combine (Pow w x) (Pow w' y) @{prf} = Pow w (Omega.combine x $ rewrite prf in y)
public export
join : {0 m, n : Form} -> ((t ^ n) ^ m) -@ (t ^ (m |*| n)) 

public export
split : (t ^ (m |*| n)) -@ ((t ^ m) *** (t ^ n))
public export
expand : (t ^ (m |*| n)) -@ (t ^ m ^ n)
public export
pure : t -@ t ^ 1
pure w = Pow w (Omega.pure w)
public export
extract : t ^ 1 -@ t
extract (Pow _ w) = Omega.extract w

-------------------
---- LEMMAS
-------------------
-------------------

export infixr 1 =@>
export infix 1 =@=
export infixl 2 ///



public export
(///) : Type -> Type -> Type
a /// b = b -@ a
export
Isomorphic t (t ^ 1) where
  ltr x = pure x
  rtl y = extract y
  ltr_rtl_id = ?ltr_rtl_id_0
  rtl_ltr_id = ?rtl_ltr_id_2


export
Isomorphic t (Pos t) where
  ltr x = ?ltr_0
  rtl y = ?rtl_0
  ltr_rtl_id = ?ltr_rtl_id_3
  rtl_ltr_id = ?ltr_rtl_id_4
