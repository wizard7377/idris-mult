module Data.Mu.Lemma

import Data.Mu.Types
import Data.Mu.Core
import Data.Mu.Util.Relude
import Data.Mu.Util.Nat
import Data.Mu.Util.LIso

private 
0 givenBoth : {0 x, y : t} -> {0 xs : M n t x} -> {0 ys : M n t y} -> (x === y) -> (xs ~=~ ys) -> (MS x xs ~=~ MS y ys)
givenBoth prf1 prf2 = let 
  prf3 : (MS x xs) === (MS x xs) = Refl
  in ?h0
export 
0 uniqueM : forall t, n, w. (a : M n t w) -> (b : M n t w) -> a === b
uniqueM MZ MZ = Refl
uniqueM (MS x xs) (MS _ ys) = let 
    prf1 : (x === x) = Refl
    prf2 : (xs === ys) = uniqueM xs ys
  in givenBoth prf1 prf2
