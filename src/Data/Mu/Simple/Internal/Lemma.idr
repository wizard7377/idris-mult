module Data.Mu.Simple.Internal.Lemma
import public Prelude.Types
import Prelude.Ops
import Prelude.Num
import Prelude.Basics
import Data.Linear.LVect
import Prelude.Uninhabited
import Data.Mu.Util.Image
import Data.Linear.LList
import Data.Mu.Classes
import Data.Linear.Notation
import Data.Nat as Data.Nat
import public Data.Nat
import Data.Linear.LNat
import Control.Function
import Prelude.Cast
import Builtin
import PrimIO 
import Data.Mu.Util.Part
import Data.Mu.Types
%auto_lazy off
%default total

%hint
0 extendsOne : {auto p : Extends x (MS y _ @{prf})} -> (x === y)
extendsOne {p = ExtendsSucc {prf} {prf' = prf'}} = prf
%hint
0 extendsTwice : {auto p : Extends x xs} -> Extends x (MS x xs @{p})
extendsTwice {p} = ExtendsSucc {prf = Refl} {prf' = p}
%hint
private 
0 transferExtendLeft : {auto prf : x === y} -> {auto rq : Extends y ys} -> Extends x ys
transferExtendLeft {prf = Refl} {rq} = rq
%hint
private 
0 transferExtendRight : {auto prf : x === y} -> {auto rq : Extends x xs} -> Extends y xs
transferExtendRight {prf = Refl} {rq} = rq

%hint
export
0 transferExtends : {t : Type} -> {n : Nat} -> {xs, ys : Lawful.M n t} -> {x, y : t} -> {auto p0 : x === y} -> {auto p1 : xs === ys} -> {auto rq : Extends x xs} -> Extends y ys
transferExtends {p0 = Refl} {p1 = Refl} {rq} = %search
%hint 
export 
0 reflLike : {xs : Lawful.M _ a} -> Like xs xs
reflLike {xs = MZ} = LikeZeroL
reflLike {xs = (MS x xs @{prf})} = %search
  
%hint
export
0 extendProd : {x, y : t} -> {xs, ys : Lawful.M n t} -> {auto p0 : x === y} -> {auto rqX : Extends x xs} -> {auto rqY : Extends y ys} -> (Like xs ys)
extendProd {p0 = Refl} {rqX=ExtendsZero} {rqY=ExtendsZero} = %search
extendProd {p0} {rqX=ExtendsSucc} {rqY=ExtendsSucc} = ?h1

%hint 
export 
0 extendSucc : {x : t} -> {xs : Lawful.M n t} -> {auto rq : Like (MS x xs) (MS y ys)} -> x === y
%hint
export
0 symLike : {auto prf : Like xs ys} -> Like ys xs
symLike {prf = LikeZeroL} = LikeZeroR
symLike {prf = LikeZeroR} = LikeZeroL
symLike {prf = LikeNext} = ?h0
