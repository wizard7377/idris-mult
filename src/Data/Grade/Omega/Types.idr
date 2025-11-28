module Data.Grade.Omega.Types


import Data.Grade.Util.Relude

import Data.Grade.Mu.Types
import Data.Grade.Form
import Decidable.Equality
import Data.Grade.Set
import Data.Linear.LVect
import Data.Grade.Mu.Lemma
import Prelude.Ops
import Data.Grade.Util.Linear
import Control.Function.FunExt
import Data.Grade.Util.Unique
import Data.Grade.Mu
import Data.Grade.Form.Sugar
%default total

public export
0 omega : (t : Type) -> (w : t) -> Type
omega t w = (1 n : QNat) -> (Mu n t w)
public export
0 omegaCps : (t : Type) -> (w : t) -> Type
omegaCps t w = (1 n : QNat) -> (forall r . (Mu n t w -@ r) -@ r)
public export
toCPS : omega t w -@ omegaCps t w
toCPS f n k = k (f {n})
public export
fromCPS : omegaCps t w -@ omega t w
fromCPS f {n} = f n (\x => x)

||| The Ω type 
||| 
||| @ p The formula of the modality 
||| @ t The underlying type
||| @ w The witness for the type

%tcinline
public export 
0 Omega1' : (p : Form) -> (t : Type) -> (w : t) -> Type
Omega1' p t w = (1 n : QNat) -> (1 prf : Solve p n) => Mu n t w
mutual
    public export
    data Omega2 : (q : Form) -> (p : Form) -> (t : Type) -> (w : t) -> Type where
        OmegaVal2 : ((1 n : QNat) -> (0 prf : QElem n ns) => Mu n (Omega1 p t w) _) -@ Omega2 (FVal ns) p t w
        OmegaVar2 : Inf ((1 p : Form) -> Omega2 p q t w) -@ Omega2 FVar q t w
        Combine2 : Omega2 p r t w -@ Omega2 q r t w -@ Omega2 (FApp AddOp p q) r t w
        Join2 : Omega2 p (FApp MulOp q r) t w -@ Omega2 (FApp MulOp p q) r t w
    public export
    data Omega1 : (p : Form) -> (t : Type) -> (w : t) -> Type where
        OmegaVal1 : ((1 n : QNat) -> (0 prf : QElem n ns) => Mu n t w) -@ Omega1 (FVal ns) t w
        OmegaVar1 : Inf ((1 p : Form) -> Omega1 p t w) -@ Omega1 FVar t w
        Combine1 : Omega1 p t w -@ Omega1 q t w -@ Omega1 (FApp AddOp p q) t w 
        Join1 : Omega2 p q t w -@ Omega1 (FApp MulOp p q) t w
  
    public export
    data QVec : QNat -> Type -> Type where
        Nil : QVec Zero a
        (::) : (1 x : a) -> (1 xs : QVec n a) -> QVec (Succ n) a

    public export
    data Omega : (p : QList Form) -> (t : Type) -> (w : t) -> Type where

        Omega0 : 
          (1 w : t) -> 
          Omega [] t w

        OmegaVal : 
          ((1 n : QNat) -> (0 prf : QElem n ns) => Mu n (Omega ps t w) _) 
          -@ Omega ((FVal ns) :: ps) t w

        OmegaVar : 
            Inf ((1 p : Form) -> Omega (p :: q) t w) -@ 
            Omega (FVar :: q) t w

        Combine : 
          Omega (p :: r) t w -@ 
          Omega (q :: r) t w -@ 
          Omega ((p |+| q) :: r) t w

        Join : 
          Omega (p :: q :: r) t w -@
          Omega ((p |*| q) :: r) t w 
{-
export 
0 UnitSeq : Consumable a => {0 x : a} -> qseq x ()
UnitSeq {x} = believe_me ()
public export
gen' : forall t. (1 src : (!* t)) -> (Omega1' FVar t {w=unrestricted src})
gen' {t} (MkBang src) {n=Zero} @{prf} = seq prf MZ
gen' {t} (MkBang src) {n=Succ n'} @{prf} = ?gen_succ
  
public export
gen1 : forall t. {1 r : Form} -> (1 src : (!* t)) -> (Omega1 r t {w=unrestricted src})
gen1 {r=FVar} src = OmegaVar1 (Delay (\p => gen1 {r=p} src))
gen1 {r=(FVal ns)} src = seq ns $ OmegaVal1 (\n => gen' src {n} @{()})
gen1 {r=(FApp AddOp p q)} (MkBang src) = Combine1 (gen1 {r=p} (MkBang src)) (gen1 {r=q} (MkBang src))
gen1 {r=(FApp MulOp p q)} (MkBang src) = Join1 ?h100

public export
genW1 : {1 r : Form} -> (src : t) -> Omega1 r t {w=src}
genW1 {r} src = gen1 {r} (MkBang src)
public export 
gen : forall t. {1 r : QList Form} -> (1 src : (!* t)) -> (Omega r t {w=unrestricted src}) 
gen {r=[]} (MkBang src) = Omega0 src
gen {r=(FVar :: q)} (MkBang src) = OmegaVar (Delay (\p => gen {r=(p :: q)} (MkBang src)))
gen {r=(FVal ns :: q)} (MkBang src) = seq ns $ OmegaVal (\n => ?gen_val)
gen {r=((FApp AddOp p q) :: r)} (MkBang src) = let 
        [r0, r1] = r.clone 2 @{ %search } @{CopyClone}  
        1 x0 : Omega (p :: r0.val) t (src) = gen {r=(p :: r0.val)} (MkBang src)
        1 x1 : Omega (q :: r1.val) t (src) = gen {r=(q :: r1.val)} (MkBang src)
    in assert_total (rewrite r0.prf in Combine x0 (rewrite cloneEq {a=r0} in x1))
gen {r=((FApp MulOp p q) :: r)} (MkBang src) = ?gen_join
export
uniqueOmega : Contractible (Omega1 p t w) 
uniqueOmega = ?unique_omega_full

public export
0 FindOmega : forall p, t, w. Omega1 p t w
FindOmega {p} {t} {w} = ?find_omega -- center' (uniqueOmega {p} {t} {w})
-}
