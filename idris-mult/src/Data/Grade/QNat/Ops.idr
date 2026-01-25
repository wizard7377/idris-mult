module Data.Grade.QNat.Ops
import Builtin
import Prelude
import Data.Linear.Notation
import Decidable.Equality
import Data.Linear.LMaybe
import Data.Grade.Logic
import Data.Linear.Interface
import Data.Grade.QNat.Types
import Data.Grade.Util.Unique
import Prelude.Clone
%default total
||| Add two linear natural numbers 
public export
ladd : QNat -@ QNat -@ QNat
ladd Zero n = n
ladd (Succ m) n = Succ (ladd m n)
public export
cadd : CNat -@ CNat -@ CNat
cadd (Fin m) (Fin n) = Fin (ladd m n)
cadd ∞ n = free n ∞
cadd m ∞ = free m ∞
||| The runtime implementation of multiplication for linear natural numbers
public export
lmul : QNat -@ QNat -@ QNat
lmul Zero n = free n Zero
lmul (Succ m) n = let 
    1 [n1, n2] = (clone 1 n)
    in ladd ((lmul m) n1.val) n2.val
public export 
cmul : CNat -@ CNat -@ CNat
cmul (Fin m) (Fin n) = Fin (lmul m n)
cmul (Fin Zero) n = free n $ Fin Zero
cmul m (Fin Zero) = free m $ Fin Zero
cmul ∞ n = free n $ ∞
cmul m ∞ = free m $ ∞
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
public export
Num CNat where
  fromInteger n = Fin (fromInteger n)
  a + b = cadd a b
  a * b = cmul a b


||| Minimum of two linear natural numbers
public export
lmin : QNat -@ QNat -@ QNat
lmin m n = go 0 m n 
  where 
    go : QNat -@ QNat -@ QNat -@ QNat
    go acc Zero n = free n acc
    go acc m Zero = free m acc
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
||| Runtime implementation of linear subtraction for linear natural numbers (Maybe for underflow) 
export
lminus : (1 k0 : QNat) -> (1 k1 : QNat) -> LMaybe QNat
lminus k0 Zero = Just k0
lminus (Succ k0) (Succ k1) = lminus k0 k1
lminus Zero (Succ k1) = free k1 Nothing
||| Greater than or equal comparison for linear natural numbers
public export 
gte : (1 x : QNat) -> (1 y : QNat) -> Bool
gte Zero y = free y False
gte (Succ x) Zero = free x True
gte (Succ x) (Succ y) = gte x y


export 
Infinite_Not_Finite : IsFinite ∞ -> Void
Infinite_Not_Finite prf impossible
export 
cadd_fin : (x : CNat) -> (y : CNat) ->  (IsFinite (cadd x y)) => (IsFinite x :*: IsFinite y )
cadd_fin (Fin x') (Fin y') @{prf} = (And (MkIsFinite x') (MkIsFinite y'))
cadd_fin (Fin x') ∞ @{prf} = absurd $ Infinite_Not_Finite (prim__believe_me ? ? prf)
cadd_fin ∞ (Fin y') @{prf} = absurd $ Infinite_Not_Finite (prim__believe_me ? ? prf)
cadd_fin ∞ ∞ @{prf} = absurd $ Infinite_Not_Finite (prim__believe_me ? ? prf)
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

public export
lrange : (1 lo : QNat) -> (1 hi : QNat) -> QNat -@ QNat
lrange lo hi n = lmin (lmax lo n) hi

%hint export
0 lmul_zero_left : (0 k : QNat) -> (lmul Zero k === Zero)
lmul_zero_left k = believe_me ()
%hint export
0 lmul_zero_right : (0 k : QNat) -> (lmul k Zero === Zero)
lmul_zero_right k = believe_me ()
%hint export
0 lmul_succ_left : (0 m, n : QNat) -> (lmul (Succ m) n === n + lmul m n)
lmul_succ_left m n = believe_me ()
%hint export
0 lmul_succ_right : (0 m : QNat) -> (0 n : QNat) -> (lmul m (Succ n) === lmul m n + m)
lmul_succ_right m n = believe_me ()

%hint 
export 
0 cadd_infinite_left : (n : CNat) -> (cadd ∞ n === ∞)
cadd_infinite_left n = let 
    0 prf : free n ∞ === ∞ = free_eq ∞
    in rewrite prf in Refl
%hint export 
0 cadd_infinite_right : (n : CNat) -> (cadd n ∞ === ∞)
cadd_infinite_right (Fin Zero) = free_eq ? 
cadd_infinite_right (Fin (Succ n')) = free_eq ?
cadd_infinite_right ∞ = free_eq ?
%hint export 
0 cadd_succ_left : (m, n : CNat) -> (cadd (CSucc m) n === CSucc (cadd m n))
cadd_succ_left (Fin m) (Fin n) = let 
  0 prf' : cadd (Fin (Succ m)) (Fin n) === Fin (Succ (ladd m n)) = Refl
  in rewrite prf' in Refl
cadd_succ_left (Fin m) ∞ = ?cadd_succ_left_finite_infinite 
cadd_succ_left ∞ n = let 
  0 prf' : cadd ∞ n === ∞ = cadd_infinite_left n
  in rewrite prf' in Refl

%hint export
cadd_zero_left : (n : CNat) -> (0 + n === n)
cadd_zero_left 0 = Refl 
cadd_zero_left (Fin n) = let 
  0 prf' : cadd (Fin Zero) (Fin n) === Fin n = Refl
  in rewrite prf' in Refl 
cadd_zero_left ∞ = rewrite cadd_infinite_left 0 in Refl
%hint export
cadd_succ_right : (m, n : CNat) -> (cadd m (CSucc n) === CSucc (cadd m n))
cadd_succ_right m n = ?cadd_succ_right_1
  
%hint export
lift_mul : (m , n : QNat) -> (Fin (lmul m n) === (cmul (Fin m) (Fin n)))
lift_mul m n = Refl

%hint export 
cmul_infinite_infinite : (cmul ∞ ∞ === ∞)
cmul_infinite_infinite = let
    0 prf : free ∞ ∞ === ∞ = free_eq ∞
    in rewrite prf in Refl
  
%hint export 
cmul_zero_left : (n : CNat) -> (cmul (Fin Zero) n === Fin Zero)
cmul_zero_left ∞ = free_eq ?
cmul_zero_left (Fin n) = let 
    0 prf' : cmul (Fin Zero) (Fin n) === Fin (lmul Zero n) = Refl
    0 prf'' : lmul Zero n === Zero = lmul_zero_left n
    in rewrite prf' in rewrite prf'' in Refl
%hint export
cmul_zero_right : (m : CNat) -> (cmul m (Fin Zero) === Fin Zero)
cmul_zero_right ∞ = free_eq ?
cmul_zero_right (Fin n) = let
    0 prf' : cmul (Fin n) (Fin Zero) === Fin (lmul n Zero) = Refl
    0 prf'' : lmul n Zero === Zero = lmul_zero_right n
    in rewrite prf' in rewrite prf'' in Refl

%hint export
cmul_succ_left : (m, n : CNat) -> ((CSucc m) * n === n + (m * n))


%hint export
cmul_infinite_nonzero_left : (n : CNat) -> (Not (n === Fin Zero)) => (cmul ∞ n === ∞)
cmul_infinite_nonzero_left n @{prf} = ?nonzero_left_1 

%hint export
cmul_infinite_nonzero_right : (m : CNat) -> (Not (m === Fin Zero)) => (cmul m ∞ === ∞)
cmul_infinite_nonzero_right m @{prf} = ?nonzero_right_1
