module Data.Grade.Exp.Ops


import Data.Grade.Util.Relude
import Data.Grade.Form
import Data.Grade.Omega.Types
import Data.Grade.Mu.Types
import Data.Grade.Exp.Types
import Data.Grade.Mu.Ops
import Decidable.Equality
import Data.Grade.Set
import Data.Linear.LVect
import Data.Grade.Mu.Lemma
import Prelude.Ops
import Data.Grade.Util.Linear
import Control.Function.FunExt
import Data.Grade.Util.Unique

%default total

namespace Exp 
    ||| Map a linear function over an Exp
    public export
    map : {0 r : t -@ u} -> (forall w. Omega p t w -@ Omega q u (r w)) -@ (t ^ p) -@ (u ^ q)
    map f (Given n x) = (Given (r n) (f x))
    public export
    box : Omega p t w -@ (t ^ p)
    box {w} x = Given w x
    public export
    unbox : (1 x : t ^ p) -> Omega p t x.fst
    unbox (Given n x) = x
    public export
    gen : (!* t) -@ (t ^ p) 
