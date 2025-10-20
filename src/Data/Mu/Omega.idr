||| Ω is so special it gets its own file ;)
module Data.Mu.Omega
import Data.Mu.Types
import Data.Mu.Util.Relude
import Data.Mu.Core 
import Data.Mu.Set
import Prelude.Ops

public export
weaken : {0 p : Set LNat} -> {0 q : Set LNat} -> (0 r : SPower p :> q) => Omega q t w -@ Omega p t w
weaken {p} {q} @{r} x {n} @{prf} = x {n} @{r {x=n} prf}
  
public export 
weaken' : Omega PTrue t w -@ Omega p t w
weaken' x {n} @{prf} = x {n} @{()}

public export 
gen' : (1 x : (!*) t) -> Omega p t (unrestricted x)
gen' x = weaken' (gen x) 
public export
simplify : Omega PTrue t w -@ omega t w
simplify x n = x {n} @{()}
public export
complicate : omega t w -@ Omega PTrue t w
complicate x {n} @{()} = x n
  
public export
reactW : {1 m, n0, n1 : LNat} -> {0 wf : ?} -> Omega (SMult m) (Mu n0 t w -@ Mu n1 u w') wf -@ Omega (SMult (m * n0)) t w -@ Omega (SMult (m * n1)) u w'
reactW {m} f x {n=v} @{prf} = ?rw0

