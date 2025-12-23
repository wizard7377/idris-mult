module Data.Grade.Exp.Types


import Data.Grade.Util.Relude
import Data.Grade.Mu.Ops
import Data.Grade.Mu.Types
import Data.Grade.List.Types
import Data.Grade.Omega.Types
import Decidable.Equality
import Data.Grade.Set
import Data.Linear.LVect
import Data.Grade.Mu.Lemma
import Prelude.Ops
import Data.Grade.Util.Linear
import Control.Function.FunExt
import Data.Grade.Util.Unique
%default total
%hide Prelude.Num.Neg
public export
Pos : Type -> Type
Pos a = {b : Type} -> (a -@ b) -@ b
public export
Neg : Type -> Type
Neg a = {b : Type} -> a -@ (b -@ b)
public export
data Exp : (ns : Form) -> Type -> Type where
  MkExp : 
    (0 w : t) ->
    Omega ns t w -@
    Exp ns t

public export
(^) : (p : Form) -> Type -> Type
(^) n t = Exp n t

public export
(^-) : (p : Form) -> Type -> Type
(^-) n t = Neg (Exp n t)

public export
(^+) : (p : Form) -> Type -> Type
(^+) n t = Pos (Exp n t)

public export
(-^) : Type -> (p : Form) -> Type
(-^) t n = Exp n (Neg t)
public export
(+^) : Type -> (p : Form) -> Type
(+^) t n = Exp n (Pos t)
