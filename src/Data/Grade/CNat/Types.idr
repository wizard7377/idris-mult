module Data.Grade.CNat.Types
import Data.Grade.Alg
import Data.Grade.QNat.Types
import Data.Grade.QNat.Ops
import Prelude 
import Decidable.Equality
import Data.Grade.Util.Linear
public export
data CNat : Type where
  Fin : (1 n : QNat) -> CNat
  Fix : CNat

%inline %tcinline
public export
∞ : CNat
∞ = Fix
public export
Consumable CNat where 
    consume (Fin n) = consume n
    consume Fix = ()
public export
Copy CNat where
    copy f (Fin n) = copy (\x, y => f (Fin x) (Fin y)) n
    copy f Fix = f Fix Fix
    copy_eq {x=(Fin n)} = copy_eq {x=n}
    copy_eq {x=Fix} = Refl
public export
finiteEq : {m : QNat} -> {n : QNat} -> (Fin m === Fin n) -> (m === n)
finiteEq Refl = Refl
public export
finiteNotInfinite : {n : QNat} -> (Fin n === Fix) -> Void
finiteNotInfinite pf = believe_me ()
public export
infiniteNotFinite : {n : QNat} -> (Fix === Fin n) -> Void
infiniteNotFinite pf = believe_me ()
public export
decEqCNat : (x : CNat) -> (y : CNat) -> Dec (x === y)
decEqCNat (Fin n) (Fin m) = case decEq n m of
    Yes prf => Yes (rewrite prf in Refl)
    No contra => No (\pf => contra (finiteEq pf))
decEqCNat Fix Fix = Yes Refl
decEqCNat Fix (Fin n) = No (\pf => infiniteNotFinite pf)
decEqCNat (Fin n) Fix = No (\pf => finiteNotInfinite pf)


public export
data CLTE : CNat -> CNat -> Type where 
  CLTE_F : (0 prf : LLTE m n) -> CLTE (Fin m) (Fin n)
  CLTE_I : CLTE _ Fix


public export
Finite : CNat -> Type
Finite n = Not (n === Fix)

public export
decFinite : (n : CNat) -> Dec (Finite n)
decFinite (Fin n) = Yes (\pf => finiteNotInfinite pf)
decFinite Fix = No (\pf => pf Refl)

