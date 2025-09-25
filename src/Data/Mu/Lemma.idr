module Data.Mu.Lemma

import Data.Mu.Types
import Data.Mu.Core
import Data.Mu.Util.Relude
import Data.Mu.Util.Nat
import Data.Mu.Util.LIso
export
zeroPower : {auto 0 x : t} -> LIso' (t ^ 0) ()
zeroPower {x=x} = MkLIso' to from
  where
    to : (t ^ 0) -@ ()
    to (Supply _ Exhaust) = ()
    
    from : () -@ (t ^ 0)
    from () = Supply x Exhaust

export
unitPower : LIso' (t ^ 1) t
unitPower = MkLIso' to from
  where
    to : (t ^ 1) -@ t
    to (Supply x (Provide x Exhaust)) = x
    
    from : t -@ (t ^ 1)
    from x = Supply x (Provide x Exhaust)
    
export
pushPull : LIso' (LPair (a ^ n) (b ^ n)) ((LPair a b) ^ n)
pushPull = MkLIso' to from
  where
    to : LPair (a ^ n) (b ^ n) -@ (LPair a b) ^ n
    to (as # bs) = ?h0
    
    from : (LPair a b) ^ n -@ LPair (a ^ n) (b ^ n)
    from xs = ?h1 
