module Data.Grade.QNat.CNat 
import Data.Grade.Alg
import Data.Grade.QNat.Types
import Data.Grade.QNat.Ops
import Prelude 
import Decidable.Equality
import Data.Grade.Util.Linear
public export
data CNat : Type where
  Finite : (1 n : QNat) -> CNat
  Infinite : CNat

Consumable CNat where 
    consume (Finite n) = consume n
    consume Infinite = ()
Copy CNat where
    copy f (Finite n) = copy (\x, y => f (Finite x) (Finite y)) n
    copy f Infinite = f Infinite Infinite
    copy_eq {x=(Finite n)} = ?ce1
    copy_eq {x=Infinite} = Refl
finiteEq : {m : QNat} -> {n : QNat} -> (Finite m === Finite n) -> (m === n)
finiteEq Refl = Refl

finiteNotInfinite : {n : QNat} -> (Finite n === Infinite) -> Void
finiteNotInfinite pf = ?h0 
infiniteNotFinite : {n : QNat} -> (Infinite === Finite n) -> Void
infiniteNotFinite pf = ?h1
decEqCNat : (x : CNat) -> (y : CNat) -> Dec (x === y)
decEqCNat (Finite n) (Finite m) = case decEq n m of
    Yes prf => Yes (rewrite prf in Refl)
    No contra => No (\pf => contra (finiteEq pf))
decEqCNat Infinite Infinite = Yes Refl
decEqCNat Infinite (Finite n) = No (\pf => infiniteNotFinite pf)
decEqCNat (Finite n) Infinite = No (\pf => finiteNotInfinite pf)

public export
0 NonZeroC : CNat -> Type
NonZeroC (Finite n) = NonZero n
NonZeroC Infinite = Unit
public export
0 nonZeroC : (x : CNat) -> Dec (NonZeroC x)
nonZeroC (Finite n) = nonZero n
nonZeroC Infinite = Yes ()
public export
data CLTE : CNat -> CNat -> Type where 
  CLTE_F : (0 prf : LLTE m n) -> CLTE (Finite m) (Finite n)
  CLTE_I : CLTE _ Infinite
public export 
cadd : CNat -@ CNat -@ CNat
cadd (Finite m) (Finite n) = Finite (ladd m n)
cadd Infinite n = seq n Infinite
cadd m Infinite = seq m Infinite
public export
cmul : CNat -@ CNat -@ CNat
cmul (Finite m) (Finite n) = Finite (lmul m n)
cmul Infinite (Finite Zero) = Finite Zero
cmul (Finite Zero) Infinite = Finite Zero
cmul a b = seq a $ seq b $ Infinite
public export
cmin : CNat -@ CNat -@ CNat
cmin (Finite m) (Finite n) = Finite (lmin m n)
cmin Infinite n = n
cmin m Infinite = m

public export
cmax : CNat -@ CNat -@ CNat
cmax (Finite m) (Finite n) = Finite (lmax m n)
cmax a b = seq a $ seq b $ Infinite

public export
Alg CNat where 
    toAlg n = Finite (mkLN (cast n))
    aeq = decEqCNat
    ALTE = CLTE
    aadd = cadd
    amul = cmul
    amin = cmin
    amax = cmax
public export
Pred CNat where 
    NonZero = NonZeroC
    nonZero = nonZeroC
    pred (Finite n) @{prf} = Finite (pred n)
    pred Infinite @{prf} = Infinite 
