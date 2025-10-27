module Data.Grade.QNat.Ops
import Builtin
import Prelude
import Data.Linear.Notation
import Data.Linear.LMaybe
import Data.Linear.Interface
import Data.Grade.QNat.Types
%default total
  
public export
ladd : QNat -@ QNat -@ QNat
ladd Zero n = n
ladd (Succ m) n = Succ (ladd m n)

public export
0 lmul' : QNat -@ QNat -@ QNat
lmul' Zero n = Zero
lmul' (Succ m) n = ladd n (lmul' m n)
export
lmul : QNat -@ QNat -@ QNat
lmul Zero n = seq n Zero
lmul (Succ m) n = let (n' :: ns) = duplicate n in ladd n' (lmul m (extract ns))

%unsafe
%hint
public export
0 mulRep : Ops.lmul === Ops.lmul' 
mulRep = believe_me ()
public export
lsub : (1 k0 : QNat) -> (1 k1 : QNat) -> (0 prf : LLTE k1 k0) => QNat
lsub k0 Zero @{prf} = k0
lsub (Succ k0) (Succ k1) @{(LLTE_S prf)} = lsub k0 k1 @{prf}
public export
Num QNat where 
    fromInteger n = mkLN (fromInteger n)
    a + b = ladd a b
    a * b = lmul a b

public export
lmin : QNat -@ QNat -@ QNat
lmin m n = go 0 m n 
  where 
    go : QNat -@ QNat -@ QNat -@ QNat
    go acc Zero n = seq n acc
    go acc m Zero = seq m acc
    go acc (Succ m) (Succ n) = go (Succ acc) m n
public export
lmax : QNat -@ QNat -@ QNat
lmax m n = go 0 m n 
  where 
    go : QNat -@ QNat -@ QNat -@ QNat
    go acc Zero n = ladd acc n
    go acc m Zero = ladd acc m
    go acc (Succ m) (Succ n) = go (Succ acc) m n
public export
lpower : QNat -@ QNat -@ QNat
lpower m Zero = seq m 1
lpower m (Succ n) = assert_total $ let 
  1 [m1, m2] = m.clone 2
  in lmul (lpower &$ m1 $ n) &$ m2
