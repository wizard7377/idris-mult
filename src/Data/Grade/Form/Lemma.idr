module Data.Grade.Form.Lemma
import Data.Linear.Notation
import Data.Grade.Util.Linear
import Data.Linear.Interface
import Relude
import Data.Grade.QNat
import Prelude.Num
import Builtin
import Prelude.Types
import Data.Linear.LVect
import Data.Linear.LMaybe
import Data.Grade.Logic
import Prelude
import Control.Relation
import Data.Grade.Form.Types
import Data.Grade.Form.Ops

public export 
Reflexive Form Unify where 
  reflexive x {n} = x
||| If p <: q and q <: r then p <: r
public export
Transitive Form Unify where 
	transitive p0 p1 x = let 
            r0 = p0 x
            r1 = p1 r0
	  in r1

  
public export
0 SolveLiteral : Solve (FVal [n]) n 
SolveLiteral = QHere 

{-

THEOREMS ON FORMULAS

-}
private 
0 CombineAdd : {a, b,c,d : QNat} -> (a = c) -> (b = d) -> (a + b = c + d)
CombineAdd Refl Refl = Refl
  
  
