module Data.Mu.Lemma

import Data.Mu.Types
import Data.Mu.Core
import Data.Mu.Util.Relude
import Data.Mu.Util.Nat
import Data.Mu.Util.LIso
import Data.Mu.Util.Equal
import Data.Mu.Util.Unique
import Data.Mu.Util.Types
import Data.Linear.LVect
%default total
||| We can, in general, lift functions on `Mu` to functions on any `Mu` 
export 
liftAM : 
  {0 proj : t -> u} ->
  (f : forall w. (1 x : Mu m t w) -> Mu n u (proj w)) -> 
  (1 x : AM m t) -> 
  AM n u
liftAM {proj} f x = map f x

 
export 
liftExistsFst :
  forall p, q.
  (f : forall a. p a -@ q a) ->
  (1 x : LExists p) -> 
  LExists q 
liftExistsFst f e = map f e
export 
liftExistsSnd :
    forall p.
    (0 f : ty -> ty) ->
    (1 x : LExists {ty} p) ->
    {auto 1 prf : {0 y : ?} -> (p y -> p (f y))} ->
    LExists {ty} p
liftExistsSnd f e @{prf} = ?h3 -- dimapExists {p=p} {q=p} f (prf {y=e}) e

private 
trans_hetro : forall a, b, c. (a ~=~ b) -> (b ~=~ c) -> (a ~=~ c)
trans_hetro Refl Refl = Refl

public export
0 uniqueEq : {n : LNat} -> {t : Type} -> {w : t} -> {a : Mu n t w} -> {b : Mu n t w} -> (a === b)
uniqueEq {n=Zero} {w=w} {a=MZ,b=MZ} = Refl 
uniqueEq {n=(Succ n')} {w=w} {a=MS w xs, b=MS w ys} = rewrite__impl 
    (\zs => MS w xs === MS w zs)
    (uniqueEq {a=ys} {b=xs})
    Refl

-- %defaulthint
public export
0 uniqueMu : Unique (Mu n t w)
uniqueMu = unique @{Example n w} @{uniqueEq}

public export
expand : {1 m : LNat} -> {1 n : LNat} -> Mu (m * n) t w -@ Mu m (Mu n t w) (Example n w)
expand {m=Zero} {n=n} xs = seq n (seqMu @{lmul_zero_left} xs MZ)
expand {m=Succ m'} {n=n} xs = let 
    1 [n0, n1] = n.clone 2
    1 [m0, m1] = m'.clone 2
    0 prf0 : ((Succ m') * n === n + (m' * n)) = lmul_succ_left
    1 xs1 : Mu (n + (m' * n)) t w = rewrite sym prf0 in xs
    1 xs1' : Mu (n + (m0.val * n) ) t w = rewrite sym m0.prf in xs1
  in ?h1
{-expand {m=Succ m'} {n=n} xs = let 
    (n' :: ns) = duplicate n
  in let 
    0 prf0 : n' === (extract ns) 
  in let 
    (y # ys) = split {m=n'} (?prf0 xs)
  in ?h0
-}
