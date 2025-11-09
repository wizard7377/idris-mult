module Data.Grade.CNat.Ops
import public Data.Grade.CNat.Types
import Data.Grade.Alg
import Relude
public export
||| When infinite 
||| @param n : CNat
WhenInf : (n : CNat) -> (1 f : QNat -@ QNat) -> (CNat -@ CNat)
WhenInf d f Fix = seq (f 0) d
WhenInf d f (Fin n) = (Fin (f n))

public export
WhenInf2 : (n : CNat) -> (1 f : QNat -@ QNat -@ QNat) -> (CNat -@ CNat -@ CNat)
WhenInf2 d f Fix y = seq y (seq (f 0 0) d)
WhenInf2 d f x Fix = seq x (seq (f 0 0) d)
WhenInf2 d f (Fin m) (Fin n) = seq d (Fin (f m n))


public export
cadd : CNat -@ CNat -@ CNat
cadd Fix Fix = Fix 
cadd Fix (Fin n) = seq (Fin n) Fix 
cadd (Fin m) Fix = seq (Fin m) Fix
cadd (Fin m) (Fin n) = Fin (ladd m n)
public export
cmul : CNat -@ CNat -@ CNat
cmul (Fin Zero) x = seq x (Fin 0)
cmul x (Fin Zero) = seq x (Fin 0)
cmul Fix Fix = Fix
cmul Fix x = seq x Fix
cmul x Fix = seq x Fix
cmul (Fin m) (Fin n) = Fin (lmul m n)
public export
cmax : CNat -@ CNat -@ CNat
cmax = WhenInf2 Fix lmax
public export
cmin : CNat -@ CNat -@ CNat
cmin Fix y = y
cmin x Fix = x
cmin (Fin m) (Fin n) = Fin (lmin m n)

%noinline
total public export
QSucc : (1 n : CNat) -> CNat
QSucc (Fin n) = Fin (Succ n)
QSucc n = n
%hint
export
0 qSuccFin : {1 n : QNat} -> (QSucc (Fin n) === Fin (Succ n))
qSuccFin {n=n} = Refl
%hint 
export 
0 finQSucc : {n : QNat} -> (Fin (Succ n) === QSucc (Fin n))
finQSucc {n} = Refl
%hint 
export 
0 fixQSucc : (Fix === QSucc Fix)
fixQSucc = Refl
%hint
export 
0 qSuccFix : (QSucc Fix === Fix)
qSuccFix = Refl
public export
Alg CNat where
    toAlg n = Fin (mkLN (fromInteger n))
    ALTE m n = CLTE m n
    aeq m n = decEqCNat m n
    aadd = cadd
    amul = cmul
public export
Trail CNat where
    amin = cmin
    amax = cmax
    aleft n = ?hpl
    aright n = ?hpr
  
public export
Count CNat where 
    NonZero (Fin n) = NonZero n
    NonZero Fix = Unit
    nonZero (Fin n) = nonZero n
    nonZero Fix = Yes ()
    APred (Fin (Succ k)) = Fin k
    APred (Fin Zero) @{prf} = ?h5
    APred Fix = Fix
    ASucc = QSucc
    

public export
0 qSuccIsSucc : forall n. (QSucc (Fin n) === Fin (Succ n))
qSuccIsSucc {n} = finQSucc

public export
0 succNotZero : {1 n : CNat} -> Not (QSucc n === Fin Zero)
succNotZero {n=Fix} prf = infiniteNotFinite prf
succNotZero {n=(Fin m)} prf = neq_succ (finiteEq prf)

public export
total
coIndNat : 
    {0 p : CNat -> Type} ->
    (base : p 0) ->
    (step : (1 x : CNat) -> (1 prev : p x) -> p (QSucc x)) ->
    (1 n : CNat) ->
    p n
coIndNat {p} base step 0 = base
coIndNat {p} base step (Fin (Succ n)) = copyWithEq go n
  where 
    go : (1 n0 : QNat) -> (1 n1 : QNat) -> (0 prf : n0 = n1) => ? 
    go n0 n1 @{prf} = let 1 r0 : p (Fin n0) = (rewrite prf in coIndNat {p=p} base step (Fin n1)) in step (Fin n0) (assert_total r0)
coIndNat {p} base step Fix = assert_total $ step Fix (coIndNat {p=p} base step Fix)
