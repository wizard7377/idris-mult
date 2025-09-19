module Basic.Tests  

import Prelude
import Data.Linear.Notation
import Data.Linear.LList
import Data.Linear.Interface
import Data.Mu
import Data.Mu.Types
import Data.Mu.Interface 
0 llength : (0 l : LList a) -> Nat
llength Nil = Z
llength (x :: xs) = S (llength xs)
mapAll' : (1 l : LList a) -> (M (llength l) (a -@ b)) -@ LList b
mapAll' Nil f = seq f Nil
mapAll' (x :: xs') f = let 
        (y # f') = use f x 
        ys = mapAll' xs' f'
        in y :: ys

NFunctor LList where
    reqF = llength
    nmap' {a, b} l f = mapAll' l f
