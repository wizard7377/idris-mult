module Data.Mu.Lawful.Internal.Core

import public Prelude.Types
import Prelude.Ops
import Prelude.Num
import Prelude.Basics
import Data.Linear.LVect
import Data.Mu.Util.Image
import Data.Mu.Util.Nat
import Data.Linear.LList
import Data.Linear.Notation
import Data.Nat as Data.Nat
import Data.Linear.LNat
import Control.Function
import Prelude.Cast
import Builtin
import PrimIO 
import Data.Mu.Util.Part
import Data.Mu.Lawful.Types
import Data.Mu.Util.Nat
import Data.Mu.Lawful.Internal.Lemma
%auto_lazy off
%default total
 
export
combine : (1 x : M a t) -> (1 y : M b t) -> {auto 0 prf : Like x y} -> M (a + b) t
combine MZ y = y
combine x MZ = castLike @{ addZeroRR } x
combine (MS x' xs @{reqX}) MZ @{prf} = 
  MS x' (combine xs MZ @{ likeSuccLeft @{reqX} @{prf} }) @{ ?h01 }
    where 
        0 combineZero : combine xs MZ ~=~ xs
        combineZero = ?h02
combine (MS x' xs @{reqX}) (MS y' ys @{reqY}) @{prf} 
  = MS x' (combine xs (MS y' ys) @{ likeSuccLeft @{reqX} @{prf} }) @{ ?h00 }
  
{-
combine x MZ = castLike @{s0} x
    where 
        s0 : {1 n : Nat} -> n === (n + Z)
        s0 {n} = case n of 
            Z => Refl
            (S k) => cong S (s0 {n = k})

-}
