module Data.Grade.QNat.Types 
import Builtin
import Prelude
import Data.Grade.Alg
import Data.Linear.Notation
import Data.Linear.Interface

import public Data.Grade.Util.Linear
import Decidable.Equality
  
||| The linear natural numbers
public export
data QNat : Type where
  ||| The zero natural number
  Zero : QNat
  ||| The successor of a natural number
  Succ : (1 k : QNat) -> QNat
public export
Consumable QNat where
  consume Zero = ()
  consume (Succ k) = consume k
public export
Duplicable QNat where
  duplicate Zero = [Zero, Zero]
  duplicate (Succ k) = Succ <$> duplicate k

public export
Copy QNat where
    copy f Zero = f Zero Zero 
    copy f (Succ k) = copy (\x, y => f (Succ x) (Succ y)) k
    copy_eq {x=Zero} = Refl
    copy_eq {x=(Succ k)} = ?ce
%default total
public export
data LLTE : QNat -> QNat -> Type where
  LLTE_Z : LLTE Zero n
  LLTE_S : (0 _ : LLTE m n) -> LLTE (Succ m) (Succ n)


%inline %tcinline public export
LN0 : QNat
LN0 = Zero 
%inline %tcinline public export
LN1 : QNat
LN1 = Succ LN0 
%inline %tcinline public export
LN2 : QNat
LN2 = Succ LN1
%inline %tcinline public export
LN3 : QNat
LN3 = Succ LN2

%inline %tcinline public export
mkLN : Nat -@ QNat
mkLN Z = LN0
mkLN (S k) = Succ (mkLN k)
export
succEq : forall m, n. (m === n) -> (Succ m === Succ n)
succEq Refl = Refl
export
succ_inj : forall m, n. (Succ m === Succ n) -> (m === n)
succ_inj Refl = Refl
%unsafe
export
neq_succ : Not (Succ m === Zero)
neq_succ prf = believe_me ()
%unsafe 
export
neq_succ' : Not (Zero === Succ n)
neq_succ' prf = believe_me ()
public export
DecEq QNat where
  decEq Zero Zero = Yes Refl
  decEq (Succ m) (Succ n) = case decEq m n of 
    Yes prf => rewrite prf in Yes Refl
    No contra => No (\prf => contra (succ_inj prf))
  decEq (Succ m) Zero = No neq_succ
  decEq Zero (Succ n) = No neq_succ'

public export
toNat : QNat -> Nat
toNat Zero = Z
toNat (Succ k) = S (toNat k)
public export
Show QNat where
  show n = show (toNat n)

public export
Show (LPair QNat QNat) where
  show (m # n) = "(" ++ show m ++ ", " ++ show n ++ ")"
public export
Eq QNat where
    Zero == Zero = True
    (Succ m) == (Succ n) = m == n
    _ == _ = False

