module Data.Grade.Omega.Ops
import Relude 
import Data.Grade.Omega.Types
import Data.Grade.Mu
import Data.Grade.List
public export
map : (f : t -@ u) -> Omega p t w -@ Omega p u (f w)
map f omega n @{prf} = Mu.map f (omega n @{prf})

public export
app : Omega p (t -@ u) w_f -@ Omega p t w_x -@ Omega p u (w_f w_x)
app omega_f omega_x n @{prf} = let 
    1 [n0, n1] = n.clone 1
    0 prf0 : Elem n0.val p = rewrite sym n0.prf in prf
    0 prf1 : Elem n1.val p = rewrite sym n1.prf in prf
    in rewrite n0.prf in Mu.app (omega_f n0.val @{prf0}) (rewrite cloneEq {a=n0} in (omega_x n1.val @{prf1}))

public export
combine : Omega p t w -@ Omega q t w -@ Omega (p |+| q) t w
combine omega1 omega2 n @{prf} = ?combine_rhs
