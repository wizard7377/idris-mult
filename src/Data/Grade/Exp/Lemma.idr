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
import Data.Grade.Mu
import Builtin
%default total
{- 
public export
0 Inv : Type -> Type
Inv t = t -@ () 
{n : QNat} -> Isomorphic (t ^ (over $ FVal' n)) (t ^^ n) where
  foward f = mapSnd foward f
  backward f = mapSnd backward f
  
private 
Isomorphic t (t ^^ 1) where 
    foward f = (Evidence f (mkMu f))
    backward (Evidence _ x) = once x
public export
{t : Type} -> Isomorphic t (t ^ 1) where 
    foward x = let 
        1 x' : t ^^ 1 = foward x
        in backward x'
    backward y = let 
        1 y' : (t ^^ 1) = foward y
        in backward y'

public export
{t : Type} -> (prf : Equiv p q) => Isomorphic (t ^ p) (t ^ q) where
    foward x = mapSnd (\x' => weaken @{snd prf} x') x
    backward y = mapSnd (\y' => weaken @{fst prf} y') y

public export
{t : Type} -> {q, p : Form} -> Isomorphic ((t ^ p) ^ q) (t ^ (q * p)) where
    foward (Evidence w x) = 
      (Evidence 
        w.fst 
        (\n => let 
            1 x' : (Mu (Eval' q n) (Exists t (Omega p t)) w) = x n
            0 xw0 : (Exists t (Omega p t)) = x'.witness
            0 xw1 : (Omega p t xw0.fst) = xw0.snd
            1 x1 : (Mu (Eval' q n) (Omega p t xw0.fst) xw1) = ?h3
            in ?h2
        )
      )
    backward (Evidence w y) = ?h1
distr_prod : ((LPair t u) ^ p)  -@ LPair (t ^ p) (u ^ p)
distr_func : (t -@ u) ^ p  -@ (t ^ p) -@ (u ^ p)
 


inverse_exp_rev : ((Inv t) ^ p) -@ (Inv (t ^ p))
inverse_exp_rev (Evidence w f) = ?ier
-}
