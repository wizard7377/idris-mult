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
0 unique : {n : Nat} -> {t : Type} -> {w : t} -> {a : Mu n t w} -> {b : Mu n t w} -> (a === b)
unique {n=Z} {w=w} {a=MZ,b=MZ} = Refl 
unique {n=(S n')} {w=w} {a=MS w xs, b=MS w ys} = rewrite__impl 
    (\zs => MS w xs === MS w zs)
    (unique {a=ys} {b=xs})
    Refl

public export 
0 unique' : forall n, n', t, t', w, w'. {auto 0 prfN : n === n'} -> {auto 0 prfT : t === t'} -> {auto 0 prfW : w ~=~ w'} -> {a : Mu n t w} -> {b : Mu n' t' w'} -> (a ~=~ b) 
unique' {a} {b} {prfN} {prfT} {prfW} = ?u0
||| We can, in general, lift functions on `Mu` to functions on `Omega`
0 combineComm : {x : Mu n t w} -> {y : Mu m t w} -> combine x y ~=~ combine y x
combineComm {x=MZ} {y=MZ} = Refl
combineComm {x=MZ} {y=MS z ys} = unique' {prfN = plusCommutative Z ?}
combineComm {x=MS z xs} {y=MZ} = ?cc1
combineComm {x=(MS z xs)} {y=(MS z ys)} = let 
  prf1 : n + m === m + n
  prf1 = plusCommutative n m
  prf2 : Mu (n + m) t w ~=~ Mu (m + n) t w
  prf2 = rewrite prf1 in Refl
  in ?h0
namespace Meta
    ||| (Γ ⊢ α) ⊢ (Γ, [w] : [t]₀ ⊢ α)
    private
    weak : (ctx -@ a) -@ ((LPair ctx (Mu 0 t w)) -@ a)
    weak f (x # MZ) = f x
    ||| (Γ, w : t ⊢ β) ⊢ (Γ, [w] : [t]₁ ⊢ β)
    private
    der : ((LPair ctx t) -@ b) -@ ((LPair ctx (Mu 1 t w)) -@ b)
    der f (x # (MS a MZ)) = f (x # a)

0 NApp : (f : (a -> b -> b)) -> (x : List a) -> (y : b) -> b
NApp f (x :: xs) y = f x (NApp f xs y)
NApp f [] y = y

liso_e1_simple' : LIso' (t ^^ 1) t
liso_e1_simple' = ?h0
