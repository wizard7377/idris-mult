module Data.Mu.LNat.Types 
import Builtin
import Prelude
import Data.Linear.Notation
import Data.Linear.Interface
import public Data.Linear.LNat
import public Data.Mu.Util.Linear
%default total
public export
data LLTE : LNat -> LNat -> Type where
  LLTE_Z : LLTE Zero n
  LLTE_S : (0 _ : LLTE m n) -> LLTE (Succ m) (Succ n)


%inline %tcinline public export
LN0 : LNat
LN0 = Zero 
%inline %tcinline public export
LN1 : LNat
LN1 = Succ LN0 
%inline %tcinline public export
LN2 : LNat
LN2 = Succ LN1
%inline %tcinline public export
LN3 : LNat
LN3 = Succ LN2

%inline %tcinline public export
mkLN : Nat -@ LNat
mkLN Z = LN0
mkLN (S k) = Succ (mkLN k)

