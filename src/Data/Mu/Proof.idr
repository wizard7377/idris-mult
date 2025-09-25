module Data.Mu.Proof
import Data.Mu.Types
import Data.Mu.Core

sourceUnique : {0 x : t} -> {0 s0, s1 : Source n x} -> (s0 === s1)
