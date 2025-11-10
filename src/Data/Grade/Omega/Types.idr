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
public export 
0 Omega : (p : Form) -> (t : Type) -> (w : t) -> Type
Omega p t w = (1 n : LVect p.vars QNat) -> (Mu (Eval' p.form n) t w)

public export
gen : forall t. (1 src : (!* t)) -> (Omega (Over 1 FVar) t {w=unrestricted src})
gen {t} (MkBang src) {n} = case n of 
  [Zero] => MZ
  [Succ n'] => MS src (gen {t=t} (MkBang src) {n=[n']})
