module Data.Mu.Proofs
import Data.Mu.Util.Iso
import Data.Mu.Types
import Data.Linear.Notation
import Data.Linear.Interface
import Data.Linear.Copies
import Data.Mu.Notation
import Prelude.Num
import Prelude.Basics
import Builtin
import Data.Nat as Nat
oneIsMultUnit : {t : Type} -> LIso (M (S Z) t) t
oneIsMultUnit = MkLIso lto lfrom
  where
    lto : M (S Z) t -@ t
    lto (MS x MZ) = x

    lfrom : t -@ M (S Z) t
    lfrom x = MS x (MZ)

zeroIsMultZero : {t : Type} -> LIso (M Z t) ()
zeroIsMultZero = MkLIso lto lfrom
  where
    lto : M Z t -@ ()
    lto MZ = ()

    lfrom : () -@ M Z t
    lfrom () = MZ
  
composeOmega : {t : Type} -> W {p=p0} t -@ (t -@ M n t) -@ W {p = (\k => n * (p0 k))} t 
multTower : {t : Type} -> {a, b : Nat} -> LIso (t ^ a ^ b) (t ^ (a * b))
multTower {a,b} = MkLIso lto lfrom
  where
    lto : (t ^ a ^ b) -@ (t ^ (mult a b))
    lto x = castEq @{multCommutative ? ?} $ joinN x

    lfrom : (t ^ (mult a b)) -@ (t ^ a ^ b)
