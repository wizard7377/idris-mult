module Data.Grade.QNat.Types 
import Builtin
import Prelude
import public Data.Grade.Alg
import Data.Linear.Notation
import Data.Linear.Interface
import public Data.Grade.Logic.QDec
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
    copy_eq {x=(Succ k)} = believe_me ()
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
%unsafe
export
neq_succ : QNot (Succ m === Zero)
neq_succ prf = assert_linear believe_me prf
%unsafe 
export
neq_succ' : QNot (Zero === Succ n)
neq_succ' prf = assert_linear believe_me prf
public export
DecEq QNat where
  decEq Zero Zero = Yes Refl
  decEq (Succ m) (Succ n) = case decEq m n of 
    Yes prf => rewrite prf in Yes Refl
    No contra => No (\prf => contra (succ_inj prf))
  decEq (Succ m) Zero = No (MkNot neq_succ)
  decEq Zero (Succ n) = No (MkNot neq_succ')
  
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
public export
QDecEq QNat where
    qDecEq {x=Zero} {y=Zero} = QYes Refl
    qDecEq {x=Succ m'} {y=Zero} = seq m' (QNo neq_succ)
    qDecEq {x=Zero} {y=Succ n'} = seq n' (QNo neq_succ')
    qDecEq {x=Succ m'} {y=Succ n'} = case qDecEq {x=m'} {y=n'} of 
        QYes prf => seq prf (QYes (rewrite prf in Refl))
        QNo contra => QNo (\prf => contra (succ_inj prf))
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
