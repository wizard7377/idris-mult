module Data.Grade.CNat.Lemma
import public Data.Grade.CNat.Types 
import public Data.Grade.CNat.Ops
import Relude
public export
0 caddComm : {1 x, y : CNat} -> (cadd x y === cadd y x)
caddComm {x=Fix} {y=Fix} = Refl
caddComm {x=Fix} {y=(Fin n)} = Refl
caddComm {x=(Fin m)} {y=Fix} = Refl
caddComm {x=(Fin m)} {y=(Fin n)} = ?cac


public export
0 caddOutLeft : cadd (QSucc x) y === QSucc (cadd x y)
caddOutLeft {x=Fix} {y=Fix} = Refl
caddOutLeft {x=Fix} {y=(Fin n)} = ?cal0
caddOutLeft {x=(Fin m)} {y=Fix} = ?cal1
caddOutLeft {x=(Fin m)} {y=(Fin n)} = ?cal2

public export
0 caddOutRight : cadd x (QSucc y) === QSucc (cadd x y)

public export
0 caddZeroLeft : cadd (Fin 0) y === y

public export
0 caddZeroRight : cadd x (Fin 0) === x

public export
0 cmulComm : {1 x, y : CNat} -> (cmul x y === cmul y x)

public export
0 cmulOutLeft : cmul (QSucc x) y === cadd (cmul x y) y
  
public export
0 cmulZeroLeft : cmul (Fin 0) y === Fin 0

public export
0 cmulZeroRight : cmul x (Fin 0) === Fin 0

public export
0 cmulSuccLeftAntiDistrib : cmul (QSucc x) y === cadd (cmul x y) y

%hint
public export
finiteZero : Finite (Fin 0)
finiteZero prf = finiteNotInfinite prf
  
%hint
public export
finiteSucc : {n : QNat} -> Finite (Fin (Succ n))
finiteSucc {n} pf = finiteNotInfinite pf

%hint 
public export
finiteQSucc : {n : CNat} -> Finite n => Finite (QSucc n)
%hint 
public export
finiteQPred : {n : CNat} -> Finite (QSucc n) => Finite n

public export
Uninhabited (Finite Fix) where
    uninhabited pf = pf Refl
