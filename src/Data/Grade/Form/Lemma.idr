module Data.Grade.Form.Lemma
import Data.Linear.Notation
import Data.Grade.Util.Linear
import Data.Linear.Interface
import Data.Grade.QNat
import Prelude.Num
import Builtin
import Prelude.Types
import Data.Linear.LVect
import Data.Linear.LMaybe
import Data.Grade.Util.LPair
import Prelude
import Control.Relation
import Data.Grade.Form.Types
import Data.Grade.Form.Ops
namespace Form 
    public export
    Id : Form
    Id = Over 1 FVar
    public export
    Lit : QNat -@ Form
    Lit n = Over 0 $ FVal n

public export 
Reflexive Form Unify where 
  reflexive x = (Element x Refl)
public export
Transitive Form Unify where 
	transitive p0 p1 x = let 
		1 (Element y0 prf0) = p0 x
		1 (Element z0 prf1) = p1 y0
		in Element z0 (rewrite prf0 in prf1)
  
  
{-

THEOREMS ON FORMULAS

-}

