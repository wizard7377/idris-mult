module Data.Grade.QNat.Lemma
import Builtin
import Prelude
import Data.Linear.Notation
import Data.Linear.Interface
  
import public Data.Grade.QNat.Types
import public Data.Grade.QNat.Ops
import Decidable.Decidable
import Data.Fun
import Data.Rel
%default total
  
  

||| If a <= b and b <= c then a <= c
public export
0 lte_trans : {a, b, c : QNat} -> LLTE a b => LLTE b c => LLTE a c

||| For any k, k <= k
public export
0 lte_refl : {k : QNat} -> LLTE k k
lte_refl {k=Zero} = LLTE_Z
lte_refl {k=Succ k'} = LLTE_S (lte_refl {k=k'})

||| For any k, k <= Succ k
public export
0 lte_succ : {a, b : QNat} -> LLTE a b => LLTE a (Succ b)
lte_succ {a} {b} @{prf} = lte_trans @{prf} @{prf' b}
  where 
    0 prf' : (x : QNat) -> LLTE x (Succ x) 
    prf' x = case x of 
      Zero => LLTE_Z
      Succ b' => assert_total $ lte_succ @{lte_refl}

||| (Succ a) <= (Succ b)  implies  a <= b
public export
0 succ_lte : {a, b : QNat} -> LLTE (Succ a) (Succ b) => LLTE a b
succ_lte {a=Zero} {b=Zero} @{prf} = LLTE_Z
succ_lte {a=Zero} {b=Succ b'} @{prf} = LLTE_Z
succ_lte {a=Succ a'} {b=Succ b'} @{prf} = case prf of 
  LLTE_S prf' => prf'
succ_lte {a=Succ a'} {b=Zero} @{prf} = ?h12

private
0 decLTE' : (x, y : QNat) -> Dec (LLTE x y)
decLTE' Zero y = Yes LLTE_Z
decLTE' (Succ x) Zero = No (\prf => noLTEZero prf)
decLTE' (Succ x) (Succ y) = case decLTE' x y of 
  Yes prf => Yes (LLTE_S prf)
  No contra => No (\prf => contra (case prf of 
    LLTE_S prf' => prf'))

||| Decidable less than or equal on QNat
%hint 
public export 
0 decLTE : {m, n : QNat} -> Dec (LLTE m n)
decLTE {m,n} = decLTE' m n


------- 

%hint export 
lmul_zero_zero : (lmul 0 0 === 0)
lmul_zero_zero = rewrite lmul_zero_left {k=Zero} in Refl
