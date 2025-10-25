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
0 lmul' : LNat -@ LNat -@ LNat
lmul' Zero n = Zero
lmul' (Succ m) n = ladd n (lmul' m n)
export
lmul : LNat -@ LNat -@ LNat
lmul Zero n = seq n Zero
lmul (Succ m) n = let (n' :: ns) = duplicate n in ladd n' (lmul m (extract ns))

%unsafe
%hint
public export
0 mulRep : Ops.lmul === Ops.lmul' 
mulRep = believe_me ()
public export
lsub : (1 k0 : LNat) -> (1 k1 : LNat) -> (0 prf : LLTE k1 k0) => LNat
lsub k0 Zero @{prf} = k0
lsub (Succ k0) (Succ k1) @{(LLTE_S prf)} = lsub k0 k1 @{prf}
public export
Num LNat where 
    fromInteger n = mkLN (fromInteger n)
    a + b = ladd a b
    a * b = lmul a b

public export
lmin : LNat -@ LNat -@ LNat
lmin m n = go 0 m n 
  where 
    go : LNat -@ LNat -@ LNat -@ LNat
    go acc Zero n = seq n acc
    go acc m Zero = seq m acc
    go acc (Succ m) (Succ n) = go (Succ acc) m n
public export
lmax : LNat -@ LNat -@ LNat
lmax m n = go 0 m n 
  where 
    go : LNat -@ LNat -@ LNat -@ LNat
    go acc Zero n = ladd acc n
    go acc m Zero = ladd acc m
    go acc (Succ m) (Succ n) = go (Succ acc) m n
