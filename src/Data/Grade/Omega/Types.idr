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
0 Omega' : (p : Form) -> (t : Type) -> (w : t) -> Type
Omega' p t w = (1 n : QNat) -> (0 prf : Solve p n) => Mu n t w
public export
data Omega : (p : Form) -> (t : Type) -> (w : t) -> Type where
    OmegaVal : ((1 n : QNat) -> (0 prf : QElem n ns) => Mu n t w) -@ Omega (FVal ns) t w
    OmegaVar : ((1 n : QNat) -> Mu n t w) -@ Omega FVar t w
    OmegaAdd : Omega p t w -@ Omega q t w -@ Omega (p |+| q) t w 
    OmegaMul : Omega' p (Omega q t w) _ -@ Omega (p |*| q) t w

export 
0 UnitSeq : Consumable a => {0 x : a} -> qseq x ()
UnitSeq {x} = believe_me ()
public export
gen' : forall t. (1 src : (!* t)) -> (Omega' FVar t {w=unrestricted src})
gen' {t} (MkBang src) {n=Zero} @{prf} = MZ
gen' {t} (MkBang src) {n=Succ n'} @{prf} = ?gen_succ
  
public export
gen : forall t. {1 r : Form} -> (1 src : (!* t)) -> (Omega r t {w=unrestricted src})
gen {r=FVar} src = OmegaVar (\n => gen' src {n} @{?h0})
gen {r=(FVal ns)} src = seq ns $ OmegaVal (\n => gen' src {n} @{UnitSeq})
gen {r=(FApp AddOp p q)} (MkBang src) = OmegaAdd (gen {r=p} (MkBang src)) (gen {r=q} (MkBang src))
gen {r=(FApp MulOp p q)} (MkBang src) = OmegaMul ?h100

public export
genW : {1 r : Form} -> (src : t) -> Omega r t {w=src}
genW {r} src = gen {r} (MkBang src)
export
uniqueOmega' : Unique' (Omega p t w)
uniqueOmega' = ?unique_omega
  
export
uniqueOmega : Unique (Omega p t w) 
uniqueOmega = ?unique_omega_full

public export
0 FindOmega : forall p, t, w. Omega p t w
FindOmega {p} {t} {w} = (Unique.witness) (uniqueOmega {p} {t} {w})
