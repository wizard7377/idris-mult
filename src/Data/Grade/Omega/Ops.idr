module Data.Grade.Omega.Ops


import Data.Grade.Util.Relude
import Data.Grade.Mu.Ops
import Data.Grade.Mu
import Data.Grade.Form
import Data.Grade.Omega.Types
import Decidable.Equality
import Data.Grade.Set
import Data.Linear.LVect
import Data.Grade.Mu.Lemma
import Prelude.Ops
import Data.Grade.Util.Linear
import Control.Function.FunExt
import Data.Grade.Util.Unique
import Data.Grade.Form.Sugar
import Prelude.Types
%default total

public export
weaken : Omega p t w -@ ((0 prf : Unify p q) => Omega q t w)
weaken f @{prf} = case f of
  OmegaVal mv => ?weaken_omega_val
  OmegaVar mv => ?weaken_omega_var
  OmegaAdd f1 f2 => ?weaken_omega_add
  OmegaMul f' => ?weaken_omega_mul

public export
combine : Omega p t w -@ Omega q t w -@ Omega (p |+| q) t w
combine f g = OmegaAdd f g

public export
join : Omega' p (Omega q t w) _ -@ Omega (p |*| q) t w
join f = OmegaMul f

public export
split : Omega (p |+| q) t w -@ (Duple (Omega p t w) (Omega q t w))
split (OmegaAdd f g) = For f g

public export
expand : Omega (p |*| q) t w -@ Omega' p (Omega q t w) _
expand (OmegaMul f) = prim__believe_me ? ? f
mutual
    public export
    app : Omega p (t -@ u) wf -@ Omega p t wx -@ Omega p u (wf wx)
    app (OmegaVal mf) (OmegaVal mx) = OmegaVal ?h0
    app (OmegaVar f) (OmegaVar x) = OmegaVar (go (OmegaVar f) (OmegaVar x))
        where 
            go : (Omega FVar (t -@ u) wf) -@ (Omega FVar t wx) -@ ((1 n : QNat) -> Mu n u (wf wx))
            go (OmegaVar mf) (OmegaVar mx) n = let 
                [n0, n1] = n.clone 2 
                in Mu.app (mf $$ n0) (mx $$ n1)
    app (OmegaAdd f1 f2) (OmegaAdd x1 x2) = combine (app f1 x1) (app f2 x2)
    app (OmegaMul f') (OmegaMul x') = ?omega_mul
    app2 : Omega p (a -@ b -@ c) wf -@ Omega p a wx -@ Omega p b wy -@ Omega p c (wf wx wy)
    app2 f x y = app (app f x) y
public export
map : {1 p : Form} -> (f : t -@ u) -> Omega p t w -@ Omega p u (f w)
map f x = app (genW f) x

public export
forget : Omega p t w -@ Omega' p t w
forget (OmegaVal mv) @{prf} n = mv @{prf} n 
forget (OmegaVar mv) @{prf} n = mv n
forget (OmegaAdd f g) @{prf} n = ?forget_omega_add
forget (OmegaMul f) @{prf} n = ?forget_omega_mul
namespace Notation
  public export
  pure : (1 w : t) -> Omega (FVal [1]) t w
  pure w = ?pure_omega 
  public export
  (<$>) : {1 p : Form} -> (f : t -@ u) -> Omega p t w -@ Omega p u (f w)
  (<$>) = map
  public export
  (<*>) : Omega p (t -@ u) wf -@ Omega p t wx -@ Omega p u (wf wx)
  (<*>) = app
