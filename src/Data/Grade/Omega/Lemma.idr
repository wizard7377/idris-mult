module Data.Grade.Omega.Lemma


import Data.Grade.Util.Relude
import Data.Grade.Mu.Ops
import Decidable.Equality
import Data.Grade.Set
import Data.Linear.LVect
import Data.Grade.Mu.Lemma
import Prelude.Ops
import Data.Grade.Util.Linear
import Control.Function.FunExt
import Data.Grade.Util.Unique
import Data.Grade.Omega.Ops
import Data.Grade.Omega.Types
import Data.Grade.Form
import Data.Grade.Mu
import Data.Grade.Util.LIso
%default total
omegaToMu : Omega (FVal n) t w -@ Mu n t w
omegaToMu x = ?h0

muToOmega : {0 n : QNat} -> Mu n t w -@ Omega (FVal n) t w
muToOmega x n @{prf} = ?h1
  
public export
{n : QNat} -> Isomorphic (Omega (FVal n) t w) (Mu n t w) where
  foward = omegaToMu
  backward = muToOmega
