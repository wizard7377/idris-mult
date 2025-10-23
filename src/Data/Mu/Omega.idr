||| Ω is so special it gets its own file ;)
module Data.Mu.Omega
import Data.Mu.Types
import Data.Mu.Util.Relude
import Data.Mu.Core 
import Data.Mu.Set
import Data.Mu.Lemma
import Prelude.Ops
import Data.Mu.Util.Linear
public export
weaken : {0 p : Set LNat} -> {0 q : Set LNat} -> (prf : p ->? q) => Omega p t w -@ Omega q t w
weaken @{prf} x {n} @{p0} = x {n} @{prf p0}
public export 
weaken' : Omega UniversalSet t w -@ Omega p t w
weaken' x {n} @{prf} = x {n} @{()}

public export 
gen' : (1 x : (!*) t) -> Omega p t (unrestricted x)
gen' x = weaken' (gen x) 
public export
simplify : Omega UniversalSet t w -@ omega t w
simplify x n = x {n} @{()}
public export
complicate : omega t w -@ Omega UniversalSet t w
complicate x {n} @{()} = x n
public export
expandOmega' : forall t. {0 w : t} -> {1 k : LNat} -> Omega (Multiple k) t w -@ Omega UniversalSet (Mu k t w) (Repeat {n=k} w)
expandOmega' {w=w} {k=k} x {n=n} @{prf} = let
        (Cloned k0 k1 prfK) = cloneWith k
        (Cloned y z prfN) = cloneWith n
        (Cloned z0 z1 prfZ) = cloneWith z
        0 prf1 : (lmul k z0 === (lmul k0 y)) = ?h0
        0 prf0 : (lmul k z0 === (lmul y k0)) = ?h5-- (rewrite (lmul_comm {m=k0} {n=y}) in prf1)
        1 x0 = x {n=(lmul y k0)} @{(MkDPair z0 ?h1)}
        1 x1 = (expand {m=z1} {n=k1} ?h4)
        0 prfZ1N : (n === z1) = trans prfN.eqAC prfZ.eqAC
        0 prfExR : (Example k w === Repeat w) = uniqueEq 
        1 x2 : (Mu n (Mu k t w) (Example k w)) = (rewrite prfZ1N in rewrite prfK.eqAC in x1)
        1 x3 : (Mu n (Mu k t w) (Repeat w)) = rewrite sym prfExR in x2
    in x3
