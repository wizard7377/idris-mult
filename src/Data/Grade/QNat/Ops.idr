module Data.Grade.QNat.Ops
import Builtin
import Prelude
import Data.Linear.Notation
import Data.Linear.LMaybe
import Data.Linear.Interface
import Data.Grade.QNat.Types
import Data.Grade.Util.Unique
%default total

||| Add two linear natural numbers 
public export
ladd : QNat -@ QNat -@ QNat
ladd Zero n = n
ladd (Succ m) n = Succ (ladd m n)

||| The runtime implementation of multiplication for linear natural numbers
export
lmul : QNat -@ QNat -@ QNat
lmul Zero n = seq n Zero
lmul (Succ m) n = let (n' :: ns) = duplicate n in ladd n' (lmul m (extract ns))

||| The runtime implementation of linear subtraction for linear natural numbers (proof of k1 <= k0 required)
public export
lsub : (1 k0 : QNat) -> (1 k1 : QNat) -> (0 prf : LLTE k1 k0) => QNat
lsub k0 Zero @{prf} = k0
lsub (Succ k0) (Succ k1) @{(LLTE_S prf)} = lsub k0 k1 @{prf}
public export
Num QNat where 
    fromInteger n = mkLN (fromInteger n)
    a + b = ladd a b
    a * b = lmul a b

||| Minimum of two linear natural numbers
public export
lmin : QNat -@ QNat -@ QNat
lmin m n = go 0 m n 
  where 
    go : QNat -@ QNat -@ QNat -@ QNat
    go acc Zero n = seq n acc
    go acc m Zero = seq m acc
    go acc (Succ m) (Succ n) = go (Succ acc) m n
||| Maximum of two linear natural numbers
public export
lmax : QNat -@ QNat -@ QNat
lmax m n = go 0 m n 
  where 
    go : QNat -@ QNat -@ QNat -@ QNat
    go acc Zero n = ladd acc n
    go acc m Zero = ladd acc m
    go acc (Succ m) (Succ n) = go (Succ acc) m n
  
||| Runtime implementation of exponentiation for linear natural numbers
export
lpower : QNat -@ QNat -@ QNat
lpower m Zero = seq m 1
lpower m (Succ n) = assert_total $ let 
  1 [m1, m2] = m.clone 2
  in lmul (lpower &$ m1 $ n) &$ m2

||| Runtime implementation of linear subtraction for linear natural numbers (Maybe for underflow) 
export
lminus : (1 k0 : QNat) -> (1 k1 : QNat) -> LMaybe QNat
lminus k0 Zero = Just k0
lminus (Succ k0) (Succ k1) = lminus k0 k1
lminus Zero (Succ k1) = seq k1 Nothing
||| Greater than or equal comparison for linear natural numbers
public export 
gte : (1 x : QNat) -> (1 y : QNat) -> Bool
gte Zero y = seq y False
gte (Succ x) Zero = seq x True
gte (Succ x) (Succ y) = gte x y

||| Runtime implementation of integral division for linear natural numbers 
||| If the reminder is non-zero, Nothing is returned
||| If the second argument is zero, Just Zero is returned
export 
ldiv : (1 x : QNat) -> (1 y : QNat) -> LMaybe QNat
ldiv x Zero = seq x $ Just Zero
ldiv Zero y = seq y $ Just Zero
ldiv x y = assert_total $ let 
  1 [x0] = x.clone 1
  1 [y0, y1] = y.clone 2
  in case lminus &$ x0 &$ y0 of 
    Nothing => seq y1 $ Nothing 
    Just r => case ldiv r &$ y1 of 
      Nothing => Nothing
      Just q => Just (Succ q)
||| Runtime implementation of pairing function for linear natural numbers
||| If a number n is of the form 2^x * 3^y, it is mapped to the pair (x, y)
||| Otherwise, it is mapped to (0, 0)
export
pairing : (1 x : QNat) -> LPair QNat QNat 
pairing Zero = seq Zero $ (Zero # Zero)
pairing n = assert_total $ let 
  1 [n0, n1] = n.clone 2
  in case (ldiv n0.val) 2 of 
    Nothing => case (ldiv n1.val) 3 of 
      Nothing => (Zero # Zero)
      Just q => let 
        (x' # y') = pairing q
        in (x' # Succ y')
    Just q => seq n1 $ let 
      (x' # y') = pairing q
      in (Succ x' # y')

--- REPRESENTATIONS

||| The ghost implementation of multiplication for linear natural numbers
public export
0 lmul' : QNat -@ QNat -@ QNat
lmul' Zero n = Zero
lmul' (Succ m) n = ladd n (lmul' m n)
||| The proof that runtime and ghost multiplication are equivalent
%unsafe
%hint
public export
0 mulRep : Ops.lmul === Ops.lmul' 
mulRep = assert_total (believe_me ())


||| The ghost implementation of exponentiation for linear natural numbers
public export
0 lpower' : QNat -@ QNat -@ QNat
lpower' m Zero = 1
lpower' m (Succ n) = lmul' (lpower' m n) m

||| The proof that runtime and ghost exponentiation are equivalent
%unsafe %hint 
public export
0 powerRep : Ops.lpower === Ops.lpower'
powerRep = believe_me ()

||| The ghost implementation of linear subtraction for linear natural numbers (Maybe for underflow)
public export
0 lminus' : (1 k0 : QNat) -> (1 k1 : QNat) -> LMaybe QNat
lminus' k0 Zero = Just k0
lminus' (Succ k0) (Succ k1) = lminus' k0 k1
lminus' Zero (Succ k1) = Nothing

||| The proof that runtime and ghost linear subtraction are equivalent
%unsafe %hint
public export
0 minusRep : Ops.lminus === Ops.lminus'
minusRep = assert_total (believe_me ())

||| The ghost implementation of integral division for linear natural numbers
public export
0 ldiv' : (1 x : QNat) -> (1 y : QNat) -> LMaybe QNat
ldiv' x Zero = Just Zero
ldiv' Zero y = Just Zero
ldiv' x y = assert_total $ case lminus' x y of 
  Nothing => Nothing
  Just r => case ldiv' r y of 
    Nothing => Nothing
    Just q => Just (Succ q)

||| The proof that runtime and ghost integral division are equivalent
%unsafe %hint 
public export
0 divRep : Ops.ldiv === Ops.ldiv'
divRep = assert_total (believe_me ())

||| The ghost implementation of pairing function for linear natural numbers
public export
0 pairing' : (1 x : QNat) -> LPair QNat QNat
pairing' 0 = (0 # 0)
pairing' n = assert_total $ case ldiv' n 2 of 
    Nothing => case ldiv' n 3 of 
        Nothing => (0 # 0)
        Just q => let 
            (x' # y') = pairing' q
            in (x' # Succ y')
    Just q => let 
        (x' # y') = pairing' q
        in (Succ x' # y')

||| The proof that runtime and ghost pairing function are equivalent
%unsafe %hint
public export
0 pairingRep : Ops.pairing === Ops.pairing'
pairingRep = assert_total (believe_me ())
