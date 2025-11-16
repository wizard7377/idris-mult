module Data.Grade.Form.Solve 

import Relude
import Data.Grade.Form.Types
import Data.Grade.Form.Ops 
import Data.Grade.Form.Lemma
import Data.Grade.Util.LPair
import Decidable.Decidable
import Decidable.Equality
import Data.Grade.QNat.QFin
mutual 
  0 DecSolveVal : (val : QNat) -> (y : QNat) -> Dec (Solve (FVal val) y)
  DecSolveVal val y = let 
        prf : Dec (val === y)
        prf = decEq val y
    in case prf of 
        Yes prf' => Yes (Element Nil prf') 
        No contra => No (\(Element [] prf') => contra prf')
  0 DecSolveVar : (y : QNat) -> Dec (Solve (FVar) y)
  DecSolveVar y = Yes (Element [y] Refl)
  0 DecSolveApp : {op : FOp} -> (p, q : Form) -> (y : QNat) -> Dec (Solve (FApp op p q) y)
  0 DecSolve : (p : Form) -> (y : QNat) -> Dec (Solve p y)
