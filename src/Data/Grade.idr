||| The `Grade` module, which contains the majority of the implementation of the types described in the paper 
||| Among these, some of the more notable are:
||| QNat: Linear natural numbers used to index graded types
||| Mu: The central "store" of graded values
||| Omega: A polymorphic variant of Mu 
||| Exponential types: Types which abstract over the witness
module Data.Grade

import public Data.Grade.Mu 
import public Data.Grade.Omega
import public Data.Grade.Exp
import public Data.Grade.QNat
import public Data.Grade.Form 
