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
Reflexive Form Equiv where 
  reflexive {x} = For (reflexive {rel=Unify} {x}) (reflexive {rel=Unify} {x}) 

public export
Symmetric Form Equiv where 
  symmetric (For p q) = For q p 

public export
Transitive Form Equiv where 
    transitive p0 p1 = let 
            (For p01 q01) = p0
            (For p12 q12) = p1
      in For (transitive {rel=Unify} p01 p12) (transitive {rel=Unify} q12 q01)
public export 
Equivalence Form Equiv where


--- BASIC LEMMAS 

%hint
notBot : Not (FVoid :> n)
