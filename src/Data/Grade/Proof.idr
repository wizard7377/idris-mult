module Data.Grade.Proof
import Data.Grade.Types
import Data.Grade.Core
import Data.Grade.Omega.Ops 
import Data.Grade.Util.Unique
import Data.Grade.Util.LIso
import Data.Grade.Util.Relude 
{-
public export
uniqueOmega : Unique (Omega' p t w)

export 
isoOmegaMuTo : {0 k : QNat} -> (1 x : Omega' (### k) t w) -> Mu k t w
isoOmegaMuTo x = x Zero
export
isoOmegaMuFrom : {0 k : QNat} -> (1 x : Mu k t w) -> Omega' (### k) t w
isoOmegaMuFrom x {n} = seq n x
public export
isoOmegaMu' : {0 k : QNat} -> LIso' (Omega' (### k) t w) (Mu k t w)
isoOmegaMu' = lIso' isoOmegaMuTo isoOmegaMuFrom
public export
isoOmegaMu : {0 k : QNat} -> LIso (Omega' (### k) t w) (Mu k t w)
isoOmegaMu = MkLIso isoOmegaMu' ?h0 ?h1

-}