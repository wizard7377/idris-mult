module Data.Grade.Omega 
import Data.Grade.Mu
import Data.Grade.Form
import Data.Grade.List
import Data.Grade.List.Lemma
import Relude
import Data.Grade.Logic
%default total
private
0 Omega' : Form -> (t : Type) -> (w : t) -> Type
Omega' ns t w = (1 n : Subset QNat (\x => IsElem x ns)) -> Mu n.fst t w
public export
data Omega : (ns : Form) -> (t : Type) -> (w : t) -> Type where
  MkOmega : Omega' ns t w -@ Omega ns t w

%hint
public export
uniqueOmega : {w : t} -> Contractible (Omega p t w)
public export
map : (f : t -@ u) -> Omega p t w -@ Omega p u (f w)
map f (MkOmega x) = MkOmega (map' f x)
  where
    map' : (f : t -@ u) -> Omega' p t w -@ Omega' p u (f w)
    map' f x prf = (Mu.map f) (x prf)
public export
app : Omega p (t -@ u) w_f -@ Omega p t w_x -@ Omega p u (w_f w_x)
app (MkOmega f) (MkOmega x) = MkOmega (app' f x)
  where
    app' : Omega' p (t -@ u) w_f -@ Omega' p t w_x -@ Omega' p u (w_f w_x)
    app' f x prf = let
        [prf0, prf1] = prf.clone 1
        f' : Mu prf.fst (t -@ u) w_f = rewrite sym prf0.prf in f prf0.val
        x' : Mu prf.fst t w_x = rewrite sym prf1.prf in x prf1.val
        in Mu.app f' x'
public export
combine : Omega p t w -@ Omega q t w -@ Omega (p |+| q) t w
combine (MkOmega x) (MkOmega y) = MkOmega (combine' x y)
  where
    combine' : Omega' p t w -@ Omega' q t w -@ Omega' (p |+| q) t w
    combine' x y prf = let
        (Elem (And (Elem v1 prf1) (Elem v2 prf2)) prf') = SolveFun @{prf}
        0 prf12 : (v1 + v2) === prf.fst = prim__believe_me ? ? prf'
        1 x' : Mu v1 t w = x (Elem v1 prf1)
        1 y' : Mu v2 t w = y (Elem v2 prf2)
        in rewrite sym prf12 in Mu.combine x' y'

public export
split : {1 n0, n1 : QNat} -> Omega [n0 + n1] t w -@ Omega [n0] t w *** Omega [n1] t w
public export
join : Omega p (Omega q t w) Point -@ Omega (p |*| q) t w
public export
expand : Omega (p |*| q) t w -@ Omega p (Omega q t w) Point
public export
sole : Mu n t w -@ Omega [n] t w
sole x = MkOmega (\(Elem n' prf) => rewrite (IsElemSingle @{ prf }) in n' >>> x)
public export
only : {1 n : QNat} -> Omega [n] t w -@ Mu n t w
only {n} (MkOmega x) = x (Elem n Here)
public export
extract : Omega [1] t w -@ t
extract x = Mu.extract $ only x


public export
pure : (1 w : t) -> Omega [1] t w
pure w = sole $ Mu.pure w
