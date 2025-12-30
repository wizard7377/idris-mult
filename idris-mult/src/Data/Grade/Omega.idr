module Data.Grade.Omega 
import Data.Grade.Mu
import Data.Grade.Form
import Data.Grade.List
import Data.Grade.List.Lemma
import Relude
import Data.Grade.Logic
%default total

public export
0 Omega : (ns : Form) -> (t : Type) -> (w : t) -> Type
Omega ns t w = (1 n : Subset QNat (\x => IsElem x ns)) -> Mu n.fst t w

public export
map : (f : t -@ u) -> Omega p t w -@ Omega p u (f w)
map f g (Elem n prf) = ?mu_map

public export
app : Omega p (t -@ u) w_f -@ Omega p t w_x -@ Omega p u (w_f w_x)
app omega_f omega_x (Elem n prf) = let
    1 [n0, n1] = n.clone 1
    0 prf0 : IsElem n0.val p = rewrite n0.prf in prf
    0 prf1 : IsElem n1.val p = rewrite n1.prf in prf
    in rewrite sym n0.prf in Mu.app (omega_f $ Elem n0.val prf0) (rewrite CloneEq {a=n0} in (omega_x $ Elem n1.val prf1))

public export
combine : Omega p t w -@ Omega q t w -@ Omega (p |+| q) t w
combine omega1 omega2 (Elem n prf) = let
  1 (For x $ Elem y prf') = App2ElemExists {z=n} @{prf}
  0 prfX = prf'.fst
  0 prfY = prf'.snd.fst
  0 prfZ = prf'.snd.snd
  1 mu1 : (Mu x t w) = omega1 (Elem x prfX )
  1 mu2 : Mu y t w = omega2 (Elem y prfY )
  1 mu3 : Mu (x + y) t w = Mu.combine mu1 mu2
  1 mu4 : Mu n t w = rewrite sym prfZ in mu3
  in mu4
mutual
    public export
    UniqueOmega : {w : t} -> Contractible (Omega p t w)
    UniqueOmega = Contract omega_example omega_unique
    private 
    omega_example : {w : t} -> Omega p t w
    omega_example {w} (Elem n prf) = Point
    private 
    omega_unique : {w : t} -> {0 omega1, omega2 : Omega p t w} -> (omega1 === omega2)
    omega_unique {w} {omega1} {omega2} = believe_me ()
public export 
split : Omega (p |+| q) t w -@ (Omega p t w) `Duple` (Omega q t w) 
split omega = ?split_rhs
public export
join : {w : t} -> Omega p (Omega q t w) (Point @{UniqueOmega}) -@ Omega (p |*| q) t w
join {w} omega1 (Elem n prf) = ?join_omega

public export
expand : 
    Omega (p |*| q) t w -@ Omega p (Omega q t w) (Point @{UniqueOmega})

public export
SingleOmegaToMu : 
  {n : QNat} ->
  Omega [n] t w -@ Mu n t w
SingleOmegaToMu omega = omega (Elem n Here)

public export
MuToSingleOmega : 
  {n : QNat} ->
  Mu n t w -@ Omega [n] t w
MuToSingleOmega = ?mu_to_single_omega_rhs 

