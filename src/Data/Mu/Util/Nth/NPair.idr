module Data.Mu.Util.Nth.NPair 
import Data.Mu
import Data.Mu.Util.LPair
import Prelude.Types
record NPair {n0 : Nat} {n1 : Nat} {ty : Type} (p : ty -> Type) where 
    constructor MkNPair
    1 fst : (ty ^ n0)
    1 snd : (p $ getWitness $ snd fst) ^ n1
  
 
