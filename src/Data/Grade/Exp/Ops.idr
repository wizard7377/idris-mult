module Data.Grade.Exp.Ops


import Data.Grade.Util.Relude
import Data.Grade.Form
import Data.Grade.Omega
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
    weaken : {0 p : Form} -> {0 q : Form} -> (prf : Unify q p) => (t ^ p) -@ (t ^ q)
    weaken @{prf} (Given n x) = Given n (Omega.weaken @{ ?weaken_prf } x)
    public export
    gen : {p : Form} -> (!* t) -@ (t ^ p) 
    gen (MkBang x) = Given x (gen (MkBang x))
    public export
    combine : {0 m, n : QNat} -> (1 x : t ^ m) -> (1 y : t ^ n) -> (x ~? y) ==> (t ^ (m |+| n))
    combine x y @{prf} = let 
      x' : Omega (formula m) t x.fst = unbox x
      y' : Omega (formula n) t y.fst = unbox y
      y'' : Omega (formula n) t x.fst = rewrite prf in y' 
      r : Omega (formula (m |+| n)) t x.fst = Omega.combine x' y''
      in box r
    public export
    join : {0 m, n : Form} -> ((t ^ n) ^ m) -@ (t ^ (m |*| n)) 
    join (Given w x) = let 
      x' : Omega (formula m) (t ^ n) _ = unbox (Given w x)
      x'' : Omega (formula m) (Omega n t _) _ = Omega.map unbox x'
      x''' : Omega' (formula m) (Omega n t w.fst) w.snd = Omega.forget x''
      r : Omega (formula (m |*| n)) t w.fst = Omega.join x'''
      in box r
