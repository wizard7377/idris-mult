module Data.Mu.LNat.Ops
import Builtin
import Prelude
import Data.Linear.Notation
import Data.Linear.Interface
import Data.Mu.LNat.Types
%default total
  
public export
ladd : LNat -@ LNat -@ LNat
ladd Zero n = n
ladd (Succ m) n = Succ (ladd m n)

public export
lmul' : LNat -> LNat -> LNat
lmul' Zero n = Zero
lmul' (Succ m) n = ladd n (lmul' m n)
public export
lmul : LNat -@ LNat -@ LNat
lmul Zero n = seq n Zero
lmul (Succ m) n = let (n' :: ns) = duplicate n in ladd n' (lmul m (extract ns))

%hint
public export
0 lmul_easy : {a, b : LNat} -> (lmul a b) = lmul' a b
lmul_easy {a=Zero} {b=Zero} = seqEq
lmul_easy {a=Zero} {b=(Succ b0)} = seqEq
lmul_easy {a=(Succ a0)} {b} = let 
    prf0 : ((lmul a0 b) = lmul' a0 b)
    prf0 = lmul_easy {a=a0} {b=b}
    prf1 : ladd b (lmul a0 b) = ladd b (lmul' a0 b)
    prf1 = rewrite prf0 in Refl
    helpf : LNat -@ LNat -@ LNat
    helpf v0 v1 = ladd b (lmul a0 v1)
    prf2 : ((let n' :: ns = duplicate b in ladd b (lmul a0 (extract ns))) = ladd b (lmul' a0 b))
    prf2 = believe_me ()
    in ?p0
public export
lsub : (1 k0 : LNat) -> (1 k1 : LNat) -> (0 prf : LLTE k1 k0) => LNat
lsub k0 Zero @{prf} = k0
lsub (Succ k0) (Succ k1) @{(LLTE_S prf)} = lsub k0 k1 @{prf}
public export
Num LNat where 
    fromInteger n = mkLN (fromInteger n)
    a + b = ladd a b
    a * b = lmul a b
