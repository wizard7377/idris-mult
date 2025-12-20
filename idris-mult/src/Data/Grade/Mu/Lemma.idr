module Data.Grade.Mu.Lemma


import Data.Grade.Util.Relude
import Data.Grade.Mu.Ops
import Data.Grade.Mu.Types
import Decidable.Equality
import Data.Grade.Set
import Data.Linear.LVect
import Prelude.Ops
import Data.Grade.Util.Linear
import Control.Function.FunExt
import Data.Grade.Util.Unique
import Data.Grade.Logic.Contract
%default total
%hint
public export
uniqueMu : {w : t} -> {1 n : QNat} -> Contractible (Mu n t w)
uniqueMu {n=Zero} = contract @{MZ} @{deforming}
  where 
    deforming : {0 y : Mu Zero t w} -> (y === MZ)
    deforming {y=MZ} = Refl

uniqueMu {w} {n=Succ n'} = contract @{MS w uniqueMu.center} @{ ?contract_proof }
    
public export
expand : {1 m : QNat} -> {1 n : QNat} -> Mu (m * n) t w -@ Mu m (Mu n t w) Point 
