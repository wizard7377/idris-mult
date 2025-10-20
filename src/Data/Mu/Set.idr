module Data.Mu.Set

import Data.Mu.Util.Relude 
import Prelude.Uninhabited
import public Data.Mu.Util.LPair

||| A set over some type, that is, `Set ty` is a predicate over `ty`
%inline %tcinline
public export
0 Set : (ty : Type) -> Type 
Set ty = (x : ty) -> Type

||| Map a predicate over `b` to a predicate over `a` via `f : a -> b`
public export
0 SMap : (a -> b) -> Set b -> Set a
SMap f p x = p (f x)

||| Combine two predicates over different types into a predicate over their product/sum
public export
0 SIntersect' : Set a -> Set b -> Set (a, b)
SIntersect' p q (x, y) = (p x, q y)
public export
0 SUnion' : Set a -> Set b -> Set (Either a b)
SUnion' p q (Left x) = p x
SUnion' p q (Right y) = q y

public export
0 SIntersect : Set a -> Set a -> Set a
SIntersect p q x = (p x, q x)
public export
0 SUnion : Set a -> Set a -> Set a
SUnion p q x = Either (p x) (q x)
public export
0 SNot : Set a -> Set a
SNot p x = Void -> p x
public export
0 STrue : Set a
STrue x = ()
public export
0 SFalse : Set a 
SFalse x = Void
public export
0 SEq : {0 a : Type} -> (x : a) -> Set a
SEq {a} x y = x === y
public export
0 SLTE : (x : LNat) -> Set LNat
SLTE x y = LLTE y x
  
||| Maps a function `t -> a -> Srop` to `\(x : a) => exists (e : t) . f e x`
public export
0 SExists : (t -> Set a) -> Set a
SExists p x = (y : t ** p y x)
||| Maps a function `a -> t` to `\(x : a) => exists (e : t) . f x = e`
public export
0 SMapTo : (a -> b) -> Set b
SMapTo f p = SExists (\y => SEq (f y)) p
public export
0 SRange : (lower : LNat) -> (upper : LNat) -> Set LNat
SRange lower upper x = (LLTE lower x, LLTE x upper)
public export
0 SMult : (fac : LNat) -> Set LNat
SMult fac = SExists (\y => (SEq (fac * y)))

||| The power set
public export
0 SPower : Set a -> Set (Set a)
SPower p q = {x : a} -> p x -> q x

%inline %tcinline public export
0 SElem : List a -> Set a
SElem [] = SFalse
SElem (y :: ys) = SUnion (SEq y) (SElem ys)
--- Sugar

export infixr 0 ->?
public export
0 (->?) : Set a -> Set (Set a)
(->?) = SPower

export infixl 1 *?
public export
0 (*?) : Set a -> Set a -> Set a
(*?) = SIntersect

export infixl 1 +?
public export
0 (+?) : Set a -> Set a -> Set a
(+?) = SUnion

export infix 1 ~?
public export
0 (~?) : a -> Set a 
(~?) = SEq

export infixl 1 <->?
public export
0 (<->?) : Set a -> Set (Set a)
(<->?) p q = ((p ->?) *? (->? p)) q
export infixl 9 :> 
public export
0 (:>) : Set a -> a -> Type
(:>) s e = s e 
  
  
--- Properties of predicates
public export
0 iffIsEquiv : (p <->? q) -> (forall x. p x <=> q x)
iffIsEquiv (prf0, prf1) = MkEquivalence prf0 prf1
public export 
0 inSubset : (p ->? q) => ({x : a} -> p x -> q x)
inSubset @{x} = x 
public export
0 trueWhen : a ->? STrue
trueWhen _ = ()
public export
0 falseWhen : SFalse ->? a
falseWhen v = absurd v
public export
0 whenLeft : (a *? b) ->? a
whenLeft (x, y) = x
public export
0 leftWhen : a ->? (a +? b)
leftWhen a = Left a
public export
0 andComm : (a *? b) ->? (b *? a)
andComm (x, y) = (y, x)
public export
0 orComm : (a +? b) ->? (b +? a)
orComm (Left x) = Right x
orComm (Right y) = Left y
public export
0 unionLeftFalse : (a +? SFalse) <->? a
unionLeftFalse = (fwd, bwd)
  where
    fwd : (a +? SFalse) ->? a
    fwd (Left x) = x
    fwd (Right v) = absurd v

    bwd : a ->? (a +? SFalse)
    bwd x = Left x
public export
0 multMult : (SMult (a * b) x) => (SMult a x)
multMult @{(MkDPair y prf)} = (MkDPair (y * b) ?mm)
