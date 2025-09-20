module Data.Mu.Lawful.Internal.Simple.Prop

import Data.Mu.Types
import Data.Mu.Lawful.Internal.Simple.Lemma
import Data.Mu.Lawful.Internal.Simple.Core
import Data.Mu.Util.Relude  
import Prelude 
export
0 combineAssoc : {x : Lawful.M m a} -> {y : Lawful.M n a} -> {auto prf : Like x y} -> ((combine x y) === (combine y x))
