module Data.Grade.Mu.Lemma


import Data.Grade.Util.Relude
import Data.Grade.Mu.Ops
import Data.Grade.Mu.Types
import Decidable.Equality
import Data.Grade.Set
import Data.Linear.LVect
import Prelude.Ops
import Data.Grade.Util.Linear
import Control.Function.FunExt
import Data.Grade.Util.Unique

%default total
 
export 
liftExistsFst :
  forall p, q.
  (f : forall a. p a -@ q a) ->
  (1 x : LExists p) -> 
  LExists q 
liftExistsFst f e = map f e
private 
trans_hetro : forall a, b, c. (a ~=~ b) -> (b ~=~ c) -> (a ~=~ c)
trans_hetro Refl Refl = Refl

private
0 uniqueEq : {n : QNat} -> {t : Type} -> {w : t} -> {a : Mu n t w} -> {b : Mu n t w} -> (a === b)
uniqueEq {n=Zero} {w=w} {a=MZ,b=MZ} = Refl 
uniqueEq {n=(Succ n')} {w=w} {a=MS w xs, b=MS w ys} = rewrite__impl 
    (\zs => MS w xs === MS w zs)
    (uniqueEq {a=ys} {b=xs})
    Refl

%hint
public export
0 uniqueMu : Unique (Mu n t w)
uniqueMu = unique @{Example n w} @{Lemma.uniqueEq}

public export
expand : {1 m : QNat} -> {1 n : QNat} -> Mu (m * n) t w -@ Mu m (Mu n t w) (Example n w)
expand {m=Zero} {n=n} xs = seq n (seqMu @{lmul_zero_left} xs MZ)
expand {m=Succ m'} {n=n} xs = let 
		1 [n0, n1] = n.clone 2
		1 [m0] = m'.clone 1
		0 prf0 : ((Succ m') * n === n + (m' * n)) = lmul_succ_left
		1 xs1 : Mu (n + (m' * n)) t w = rewrite sym prf0 in xs
		1 (xs2 # xs3) : (LPair (Mu n0.val t w) (Mu (lmul m' n) t w)) = split {m=n0.val} (rewrite sym n0.prf in xs1)
		1 ys : Mu n t w = rewrite n0.prf in xs2
		1 zs : Mu (lmul m' n) t w = xs3	
		1 zs0 : Mu m0.val (Mu n t w) (Example ? w) = assert_total (rewrite n1.prf in expand {m=m0.val} {n=n1.val} (rewrite sym n1.prf in rewrite sym m0.prf in zs)) -- TODO prove this is total
		1 zs1 : Mu m' (Mu n t w) (Example n w) = rewrite m0.prf in zs0
		0 prf1 : (Example n w === ys) = Lemma.uniqueEq
	in rewrite prf1 in MS ys (rewrite sym prf1 in zs1)
{-expand {m=Succ m'} {n=n} xs = let 
    (n' :: ns) = duplicate n
  in let 
    0 prf0 : n' === (extract ns) 
  in let 
    (y # ys) = split {m=n'} (?prf0 xs)
  in ?h0
-}
