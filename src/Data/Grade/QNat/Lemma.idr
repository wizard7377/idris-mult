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

||| m + n = n + m 
public export
0 addComm : {m, n : QNat} -> (ladd m n = ladd n m)
||| (0 * k) = 0
public export
0 lmul_zero_left' : forall k. (lmul' Zero k = Zero)
lmul_zero_left' {k} = Refl
||| k * 0 = 0
public export
0 lmul_zero_right' : forall k. (lmul' k Zero = Zero)
lmul_zero_right' {k=Zero} = Refl
lmul_zero_right' {k=Succ k'} = rewrite lmul_zero_right' {k=k'} in Refl


||| 0 * k = 0 (runtime version)
%defaulthint
public export
0 lmul_zero_left : forall k. (lmul Zero k = Zero)
lmul_zero_left {k} = rewrite mulRep in lmul_zero_left' {k}

||| (S m) * n = n + (m * n)  
public export
0 lmul_succ_left' : forall m, n. (lmul' (Succ m) n = ladd n (lmul' m n)) 
lmul_succ_left' {m} {n} = Refl

||| (S m) * n = n + (m * n)  (runtime version)
%defaulthint
public export
0 lmul_succ_left : forall m, n. (lmul (Succ m) n = ladd n (lmul m n))
lmul_succ_left {m} {n} = rewrite mulRep in lmul_succ_left' {m} {n}

||| x * y = y * x
public export
0 lmul_comm' : forall m, n. (lmul' m n = lmul' n m)
lmul_comm' {m = Zero} {n} = rewrite lmul_zero_right' {k=n} in Refl

||| x * y = y * x (runtime version)
public export
0 lmul_comm : forall m, n. (lmul m n = lmul n m)
lmul_comm {m} {n} = rewrite mulRep in lmul_comm' {m} {n}

public export
0 pair_power' : {x, y : QNat} -> (pairing' ((lpower 2 x) * (lpower 3 y)) === (x # y))
pair_power' = ?zz0
public export
0 surj_pair : {x, y : QNat} -> (n : QNat ** (pairing' n === (x # y)))
surj_pair {x} {y} = MkDPair ((lpower 2 x) * (lpower 3 y)) (pair_power' {x} {y})

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

||| a + b = c implies a <= c
public export
0 lte_sum_l : {a, b, c : QNat} -> (a + b = c) -> LLTE a c
||| a + b = c implies b <= c
public export
0 lte_sum_r : {a, b, c : QNat} -> (a + b = c) -> LLTE b c
