module Data.Grade.QNat.Lemma
import Builtin
import Prelude
import Data.Linear.Notation
import Data.Linear.Interface
  
import public Data.Grade.QNat.Types
import public Data.Grade.QNat.Ops

%default total
public export
0 lmul_zero_left' : forall k. (lmul' Zero k = Zero)
lmul_zero_left' {k} = Refl
||| x * 0 = 0
public export
0 lmul_zero_right' : forall k. (lmul' k Zero = Zero)
lmul_zero_right' {k=Zero} = Refl
lmul_zero_right' {k=Succ k'} = rewrite lmul_zero_right' {k=k'} in Refl


||| 0 * x = 0 (runtime version)
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
pair_power' = ?h0
public export
0 surj_pair : {x, y : QNat} -> (n : QNat ** (pairing' n === (x # y)))
surj_pair {x} {y} = MkDPair ((lpower 2 x) * (lpower 3 y)) (pair_power' {x} {y})
