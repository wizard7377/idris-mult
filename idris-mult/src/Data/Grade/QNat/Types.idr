module Data.Grade.QNat.Types 
import Builtin
import Prelude
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
Drop QNat where
  drop Zero = ()
  drop (Succ k) = drop k
public export
Duplicable QNat where
  duplicate Zero = [Zero, Zero]
  duplicate (Succ k) = Succ <$> duplicate k

public export
Copy QNat where
    copy Zero f = f Zero Zero 
    copy (Succ k) f = copy k (\x, y => f (Succ x) (Succ y))
%default total
||| The less than or equal relation on QNat
public export
data LLTE : QNat -> QNat -> Type where
  ||| Zero <= n
  LLTE_Z : LLTE Zero n
  ||| If m <= n then Succ m <= Succ n
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
succ_inj : forall m, n. (Succ m === Succ n) -@ (m === n)
succ_inj Refl = Refl
  
private 
use_absurd : Void -@ a
use_absurd v impossible
%unsafe
export
neq_succ : Not (Succ m === Zero)
neq_succ prf = assert_linear believe_me prf
%unsafe 
export
neq_succ' : Not (Zero === Succ n)
neq_succ' prf = assert_linear believe_me prf
public export
DecEq QNat where
  decEq Zero Zero = Yes Refl
  decEq (Succ m) (Succ n) = case decEq m n of 
    Yes prf => rewrite prf in Yes Refl
    No contra => No (\prf => contra (succ_inj prf))
  decEq (Succ m) Zero = No ?dec_eq_1
  decEq Zero (Succ n) = No ?dec_eq_2
  
public export
noLTEZero : {n : QNat} -> Not (LLTE (Succ n) Zero)
noLTEZero prf = believe_me ()

||| Decidable less than or equal on QNat
public export
0 DecLTE : {m, n : QNat} -> Dec (LLTE m n)
DecLTE {m=Zero} {n=n} = Yes LLTE_Z
DecLTE {m=Succ m'} {n=Zero} = No (\prf => noLTEZero prf)
DecLTE {m=Succ m'} {n=Succ n'} = case DecLTE {m=m'} {n=n'} of 
  Yes prf => Yes (LLTE_S prf)
  No contra => No (\prf => contra (case prf of LLTE_S prf' => prf'))

||| Convert QNat to Nat
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
