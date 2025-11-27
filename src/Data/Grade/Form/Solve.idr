module Data.Grade.Form.Solve 

import Relude
import Data.Grade.Form.Types
import Data.Grade.Form.Ops 
import Data.Grade.Form.Lemma
import Data.Grade.Logic
import Decidable.Decidable
import Decidable.Equality
import Data.Grade.QNat.QFin
parameters (1 y : QNat)
    mutual 
        0 DecSolveOpGTE : (op : FOp) -> (1 f, g : Form) -> (1 n : QNat) -> QDec (SolveAbove (FApp op f g) n)
        0 DecSolveValGTE : (1 n : QNat) -> QDec (SolveAbove (FVal n) y)
        0 DecSolveVarGTE : QDec (SolveAbove FVar y)
        0 DecSolveGTE : (1 f : Form) -> (1 n : QNat) -> QDec (SolveAbove f n)
        DecSolveVal : {1 n : QNat} -> QDec (Solve (FVal n) y)
        DecSolveVal {n} = case qDecEq {x=n} {y=y} of 
            QYes prf => seq prf (QYes (Elem [] prf))
            QNo prf => QNo (\(Elem [] prf') => seq (prf (scandel prf')) (efalse (prf prf')))
        DecSolveVar : QDec (Solve FVar y)
        DecSolveVar = QYes (Elem [y] Refl)
        DecSolveOp : (1 op : FOp) -> (1 f, g : Form) -> QDec (Solve (FApp op f g) y)
        DecSolveOp op f g = ?hdso
            

          
        0 DecSolve : (1 f : Form) -> QDec (Solve f y)
