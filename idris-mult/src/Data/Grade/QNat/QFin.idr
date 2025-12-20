module Data.Grade.QNat.QFin 
import public Data.Grade.QNat.Types
import public Data.Grade.QNat.Lemma
import public Data.Grade.QNat.Ops
import Data.Grade.Logic
import Relude
import Decidable.Equality
public export
QFin : (hi : QNat) -> Type
QFin hi = Subset QNat (\k => LLTE k hi) 


public export
qfin : {0 hi : QNat} -> (1 k : QNat) -> (0 prf : LLTE k hi) => QFin hi
qfin {hi} k @{prf} = Elem k prf

public export
weaken : (0 prf : LLTE hi hi') => QFin hi -@ QFin hi'
weaken @{prf} (Elem k prfK) = Elem k (lte_trans @{prfK} @{prf})
public export
(.val) : {0 hi : QNat} -> QFin hi -@ QNat
(.val) {hi} (Elem k prf) = k

private 
0 limit_lte : (LLTE x (Succ y)) -> Not (x === Succ y) -> LLTE x y  
limit_lte (LLTE_Z) nEq = LLTE_Z
limit_lte (LLTE_S prf) nEq = ?lle
%noinline
public export
0 Bounded : (hi : QNat) -> (prop : QNat -> Type) -> Type
Bounded hi prop = Exists (QFin hi) (\k => prop k.fst)

public export
0 ZeroBound : Bounded Zero prop -> prop Zero
ZeroBound (Given (Elem Zero LLTE_Z) pZ) = pZ
public export
0 AddProof : Dec (prop (Succ hi)) -> Dec (Bounded hi prop) -> Dec (Bounded (Succ hi) prop)
AddProof (Yes pSucc) _ = Yes (Given (Elem (Succ hi) (lte_refl {k=Succ hi})) pSucc)
AddProof (No nSucc) (Yes (Given (Elem k prfK) pK)) = Yes (
    Given (Elem k ?h0) ?h1)
AddProof (No nSucc) (No nBound) = No contra 
  where 
    contra : (Bounded (Succ hi) prop) -> Void
    contra (Given (Elem k prfK) pK) = case decEq k (Succ hi) of 
        Yes eq => nSucc (rewrite sym eq in pK)
        No neq => let 
            nBound' = NegationExists nBound
            in nBound' ?h10
public export
0 Limited : {prop : QNat -> Type} -> (ask : (k : QNat) -> Dec (prop k)) -> (hi : QNat) -> Dec (Bounded hi prop) 
Limited ask Zero = case ask Zero of 
    Yes pp => Yes (Given (Elem Zero LLTE_Z) pp)
    No np => No (\contra => np (ZeroBound {prop=prop} contra))
Limited ask (Succ hi') = AddProof {prop=prop} (ask (Succ hi')) (Limited ask hi')

public export
finMinus : (1 x : QNat) -> (1 y : QFin x) -> QNat 
finMinus Zero (Elem Zero prf) = Zero
finMinus (Succ x') (Elem (Succ k) prf) = finMinus x' (Elem k (succ_lte @{prf}))
finMinus (Succ x') (Elem Zero prf) = (Succ x')
