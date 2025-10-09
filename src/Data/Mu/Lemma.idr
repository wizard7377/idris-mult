module Data.Mu.Lemma

import Data.Mu.Types
import Data.Mu.Core
import Data.Mu.Util.Relude
import Data.Mu.Util.Nat
import Data.Mu.Util.LIso
import Data.Mu.Util.Equal
import Data.Mu.Util.Types
%default total
||| We can, in general, lift functions on `Mu` to functions on any `Mu` 
export 
liftAM : 
  {0 proj : t -> u} ->
  (f : forall w. (1 x : Mu m t w) -> Mu n u (proj w)) -> 
  (1 x : AM m t) -> 
  AM n u
liftAM {proj} f x = dimapExists f x

 
export 
liftExistsFst :
  forall p, q.
  (f : forall a. p a -@ q a) ->
  (1 x : LExists p) -> 
  LExists q 
liftExistsFst f e = dimapExists f e
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

%hint
public export 
0 unique : {a : Mu n t w} -> {b : Mu n t w} -> (a === b)
unique {a=MZ,b=MZ} = Refl 
unique {a=MS x xs, b=MS x ys} = let 
  prf1 : x === x
  prf1 = Refl
  prf2 : xs === ys
  prf2 = unique {a=xs,b=ys}
  prf3 : MS x xs === MS x ys
  in prf3
  
||| We can, in general, lift functions on `Mu` to functions on `Omega`
export 
liftW : 
    {0 p, q : Nat -@ Nat} -> 
    (f : forall n. (1 x : Mu n t w) -> Mu (p n) u w') -> 
    (1 x : Omega q t w) -> 
    Omega (LCompose q p) u w'
liftW {p} {q} f x m = f (x m)
export
liftAW : 
    {0 proj : t -> u} ->
    (f : forall w. (1 x : Omega p t w) -> Omega q u (proj w)) -> 
    (1 x : AW p t) -> 
    AW q u
liftAW {proj} f x = dimapExists f x


0 combineComm : {x : Mu n t w} -> {y : Mu m t w} -> combine x y ~=~ combine y x
combineComm {x} {y} = let 
  prf1 : n + m === m + n
  prf1 = plusCommutative n m
  prf2 : Mu (n + m) t w ~=~ Mu (m + n) t w
  prf2 = rewrite prf1 in Refl
  in ?h0 $ unique {a=combine x y, b=rewrite prf2 in combine y x}
