module Data.Mu.LNat.Lemma
import Builtin
import Prelude
import Data.Linear.Notation
import Data.Linear.Interface
  
import public Data.Mu.LNat.Types
import public Data.Mu.LNat.Ops
%default total
 
||| 0 = 0 
-- %defaulthint
public export
zero_eq_zero : Zero = Zero
zero_eq_zero = Refl
||| Succ k0 = Succ k1  implies k0 = k1
-- %defaulthint
public export
0 succ_eq_succ : (k0 = k1) => (Succ k0) = (Succ k1)
succ_eq_succ @{Refl} = Refl
-- %defaulthint
public export
0 succ_qe_succ : (Succ k0 = Succ k1) => k0 = k1
succ_qe_succ @{Refl} = Refl
-- %defaulthint
public export 
0 zero_lte_n : LLTE Zero n
zero_lte_n = LLTE_Z
-- %defaulthint
public export 
0 succ_lte_succ : (LLTE m n) => LLTE (Succ m) (Succ n)
succ_lte_succ @{prf} = LLTE_S prf
-- %defaulthint
public export
0 succ_elt_succ : LLTE (Succ m) (Succ n) => LLTE m n
succ_elt_succ @{LLTE_S prf} = prf
-- %defaulthint
public export
0 sym_qeq : (k0 = k1) => (k1 = k0)
sym_qeq @{Refl} = Refl
-- %defaulthint
public export
0 trans_qeq : (k0 = k2) => (k1 = k2) => (k0 = k2)
trans_qeq @{Refl} @{Refl} = Refl

------ On addition
-- %defaulthint
public export 
0 ladd_zero_right : {k : LNat} -> (ladd k Zero) = k
ladd_zero_right {k=Zero} = Refl 
ladd_zero_right {k=(Succ k0)} = let 
    prf : ((ladd k0 Zero) = k0)
    prf = ladd_zero_right {k=k0}
    in rewrite prf in Refl
-- %defaulthint
public export 
0 ladd_zero_left : {k : LNat} -> (ladd Zero k) = k
ladd_zero_left {k} = Refl
-- %defaulthint
public export 
0 ladd_succ_right : {k0, k1 : LNat} -> (ladd k0 (Succ k1)) = Succ (ladd k0 k1)
ladd_succ_right {k0=Zero} {k1} = Refl
ladd_succ_right {k0=(Succ k0')} {k1} = let 
    prf : ((ladd k0' (Succ k1)) = Succ (ladd k0' k1))
    prf = ladd_succ_right {k0=k0'} {k1=k1}
    in rewrite prf in Refl
-- %defaulthint
public export 
0 ladd_succ_left : {k0, k1 : LNat} -> (ladd (Succ k0) k1) = Succ (ladd k0 k1)
ladd_succ_left {k0} {k1} = Refl
-- %defaulthint
public export 
0 ladd_commutative : {k0, k1 : LNat} -> (ladd k0 k1) = (ladd k1 k0)
ladd_commutative {k0=Zero} {k1=Zero} = Refl 
ladd_commutative {k0=Zero} {k1=Succ k1'} = let
        prf : (k1' = (ladd k1' Zero))
        prf = sym $ ladd_zero_right {k=k1'}
    in succ_eq_succ @{prf}
ladd_commutative {k0=Succ k0'} {k1=Zero} = let 
    prf : (ladd k0' Zero = k0') 
    prf = ladd_zero_right {k=k0'}
  in succ_eq_succ @{prf}
ladd_commutative {k0=Succ k0'} {k1=Succ k1'} = let 
        prf : (ladd k0' (Succ k1') = (ladd k1' (Succ k0')))
    in succ_eq_succ @{prf}

-- %defaulthint
public export 
0 lmul_zero_right : {k : LNat} -> (lmul k Zero) = Zero
lmul_zero_right {k=Zero} = seqEq
lmul_zero_right {k=(Succ k0)} = let 
    prf : (lmul k0 (extract [Zero]) = Zero)
    prf = rewrite__impl (\x => (lmul k0 x = Zero)) extractEq (lmul_zero_right {k=k0})
  in prf
-- %defaulthint
public export 
0 lmul_zero_left : {k : LNat} -> (lmul Zero k) = Zero
lmul_zero_left {k} = seqEq
 
-- %defaulthint
public export 
0 lmul_succ_left : (lmul (Succ k0) k1) = (ladd k1 (lmul k0 k1))
lmul_succ_left = ?lsl0
{-
-- -- %defaulthint
public export 
-- -- %defaulthint
public export 
-- -- %defaulthint
public export 
-- -- %defaulthint
public export 
-- -- %defaulthint
public export 
-- -- %defaulthint
public export 
-- -- %defaulthint
public export 
-- -- %defaulthint
public export 
-- -- %defaulthint
public export 
-- -- %defaulthint
public export 
-- -- %defaulthint
public export 
-- -- %defaulthint
public export 
-- -- %defaulthint
public export 
-- -- %defaulthint
public export 
-}
