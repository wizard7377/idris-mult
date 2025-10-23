module Data.Mu.LNat.Lemma
import Builtin
import Prelude
import Data.Linear.Notation
import Data.Linear.Interface
  
import public Data.Mu.LNat.Types
import public Data.Mu.LNat.Ops
%default total
public export
0 lmul_zero_left' : forall k. (lmul' Zero k = Zero)
lmul_zero_left' {k} = Refl

%defaulthint
public export
0 lmul_zero_left : forall k. (lmul Zero k = Zero)
lmul_zero_left {k} = rewrite mulRep in lmul_zero_left' {k}
  
public export
0 lmul_succ_left' : forall m, n. (lmul' (Succ m) n = ladd n (lmul' m n)) 
lmul_succ_left' {m} {n} = Refl
%defaulthint
public export
0 lmul_succ_left : forall m, n. (lmul (Succ m) n = ladd n (lmul m n))
lmul_succ_left {m} {n} = rewrite mulRep in lmul_succ_left' {m} {n}

public export
0 lmul_comm' : forall m, n. (lmul' m n = lmul' n m)

public export
0 lmul_comm : forall m, n. (lmul m n = lmul n m)
