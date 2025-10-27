module Data.Grade.Exp.Lemma


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
import Data.Grade.Exp.Types
import Data.Grade.Util.LIso
import Data.Grade.Form
import Data.Grade.Omega
%default total
  
public export
exp_pow : LIso' ((t ^ p) ^ q) (t ^ (p * q))

prod_pow : (1 x : (t ^ p)) -> (1 y : (t ^ q)) -> (0 prf : x ~? y) => (t ^ (p + q))
public export
one_exp : LIso' (t ^ 1) t

distr_prod : ((LPair t u) ^ p)  -@ LPair (t ^ p) (u ^ p)

distr_func : (t -@ u) ^ p  -@ (t ^ p) -@ (u ^ p)


