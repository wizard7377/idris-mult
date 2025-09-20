module Data.Mu.Lawful.Proofs
import Data.Mu.Util.Iso
import Data.Mu.Lawful.Types
import Data.Linear.Notation
import Data.Linear.Interface
import Data.Linear.Copies
import Data.Mu.Lawful.Notation
import Prelude.Num
import Prelude.Basics
import Builtin
import Data.Nat as Nat
oneIsMultUnit : {t : Type} -> LIso (Lawful.M (S Z) t) t
oneIsMultUnit = MkLIso lto lfrom
  where
    lto : Lawful.M (S Z) t -@ t
    lto (MS x MZ) = x

    lfrom : t -@ Lawful.M (S Z) t
    lfrom x = MS x (MZ)

zeroIsMultZero : {t : Type} -> LIso (Lawful.M Z t) ()
zeroIsMultZero = MkLIso lto lfrom
  where
    lto : Lawful.M Z t -@ ()
    lto MZ = ()

    lfrom : () -@ Lawful.M Z t
    lfrom () = MZ
  
composeOmega : {t : Type} -> W {p=p0} t -@ (t -@ Lawful.M n t) -@ W {p = (\k => n * (p0 k))} t 
multTower : {t : Type} -> {a, b : Nat} -> LIso (t ^ a ^ b) (t ^ (a * b))
multTower {a,b} = MkLIso lto lfrom
  where
    lto : (t ^ a ^ b) -@ (t ^ (mult a b))
    lto x = castEq @{multCommutative ? ?} $ joinN' x

    lfrom : (t ^ (mult a b)) -@ (t ^ a ^ b)
