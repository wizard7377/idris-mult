module Data.Grade.Omega.Ops


import Data.Grade.Util.Relude
import Data.Grade.Mu.Ops
import Data.Grade.Mu
import Data.Grade.Form
import Data.Grade.Omega.Types
import Decidable.Equality
import Data.Grade.Set
import Data.Linear.LVect
import Data.Grade.Mu.Lemma
import Prelude.Ops
import Data.Grade.Util.Linear
import Control.Function.FunExt
import Data.Grade.Util.Unique
import Data.Grade.Form.Sugar
import Prelude.Types
%default total

public export
combine : Omega (p :: r) t w -@ Omega (q :: r) t w -@ Omega ((FAdd p q) :: r) t w
combine = Combine
public export
split : Omega ((FAdd p q) :: r) t w -@ Duple (Omega (p :: r) t w) (Omega (q :: r) t w)
split (Combine x y) = (For x y) 
private
reflect : {1 p : Form} -> Omega (p :: r) t w -@ Omega r (Omega [p] t w) ?ref
reflect {p = FTop} x = ?reflect_rhs_0
reflect {p = FBot} x = ?reflect_rhs_1
reflect {p = (FVal y)} x = ?reflect_rhs_2
reflect {p = (FAlt p q)} x = ?reflect_rhs_3
reflect {p = (FAdd p q)} x = ?reflect_rhs_4
reflect {p = (FMul p q)} x = ?reflect_rhs_5
