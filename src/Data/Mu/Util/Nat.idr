module Data.Mu.Util.Nat

import Prelude 
import Data.Nat 

%default total
export 
addSucc2 : ((S (S (a + b))) === (S a + S b))
addSucc2 = cong S $ plusSuccRightSucc ? ?

%hint 
export 
addZeroLL : ((Z + n) === n)
addZeroLL = Refl
%hint
export
addZeroLR : {n : Nat} -> ((n + Z) === n)
addZeroLR {n = Z} = Refl
addZeroLR {n = (S k)} = cong S (addZeroLR {n = k})
%hint 
export 
addZeroRL : (n === (Z + n))
addZeroRL = Refl
%hint
export
addZeroRR : {n : Nat} -> (n === (n + Z))
addZeroRR {n = Z} = Refl
addZeroRR {n = (S k)} = cong S (addZeroRR {n = k})
