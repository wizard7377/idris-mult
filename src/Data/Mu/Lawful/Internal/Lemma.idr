module Data.Mu.Lawful.Internal.Lemma
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
import Data.Mu.Lawful.Types
%auto_lazy off
%default total

%hint
export 
0 extendsZero : {a : Type} -> {0 x : a} -> Extends x MZ
extendsZero {a} {x} = ExtendsZero
%hint 
export
0 extendsSucc : {auto p0 : x = y} -> {auto p1 : Extends y ys} -> Extends x (MS y ys @{p1})
extendsSucc {x} {y} {ys} {p0} {p1} = ExtendsSucc @{p0} @{p1}
%hint 
export 
0 extendsTwice : {auto p0 : Extends x y} -> Extends x (MS x y @{p0})
extendsTwice {x} {y} {p0} = ExtendsSucc @{Refl} @{p0}

%hint
export 
0 extendsLike : {0 y, z : M n t} -> {auto p0 : Extends x y} -> {auto p1 : Extends x z} -> Like y z
extendsLike {p0=ExtendsZero} {p1} = LikeZeroR
extendsLike {p0} {p1=ExtendsZero} = LikeZeroL
extendsLike {p0=ExtendsSucc @{prfY} @{reqY}} {p1=ExtendsSucc @{prfZ} @{reqZ}} = LikeSucc @{s0} @{reqY} @{reqZ}
  where 
    s0 = (trans (sym prfY) (prfZ))


private
0 extendsLeftEq : {0 x, y : a} -> {0 xs : M n a} -> {auto p0 : x === y} -> {auto p1 : Extends x xs} -> Extends y xs
extendsLeftEq {x} {y} {xs} {p0} {p1} = rewrite sym p0 in p1

private 
0 extendsRightEq : {0 x : a} -> {0 xs, ys : M n a} -> {auto p0 : xs === ys} -> {auto p1 : Extends x xs} -> Extends x ys
extendsRightEq {x} {xs} {ys} {p0} {p1} = rewrite sym p0 in p1

%hint 
export
0 extendsEq : {0 x, y : a} -> {0 xs, ys : M n a} -> {auto p0 : x === y} -> {auto p1 : xs === ys} -> {auto p2 : Extends x xs} -> Extends y ys
extendsEq {x} {y} {xs} {ys} {p0} {p1} {p2} = rewrite sym p0 in rewrite sym p1 in p2

%hint 
export 
0 likeSucc : {0 x, y : t} -> {0 xs, ys : M n t} -> {auto reqX : Extends x xs} -> {auto reqY : Extends y ys} -> {auto prf0 : Like (MS x xs @{reqX}) (MS y ys @{reqY})} -> Like xs ys
likeSucc {reqX=ExtendsZero} = LikeZeroR
likeSucc {reqY=ExtendsZero} = LikeZeroL
likeSucc 
  {reqX=ExtendsSucc @{prfX} @{reqXs}} {reqY=ExtendsSucc @{prfY} @{reqYs}} 
  {prf0=LikeSucc @{prf1} @{ExtendsSucc} @{ExtendsSucc }} = rewrite sym prfX in rewrite sym prfY in ?h0

%hint
export
0 likeSuccLeft : 
  {0 x : t} -> {0 xs : M m t} -> {0 y : M n t} -> 
  {auto reqX : Extends x xs} -> 
  {auto prf0 : Like (MS x xs) y} ->
  Like xs y
likeSuccLeft = %search

%hint 
export 
0 likeSuccRight : 
  {0 y : t} -> {0 ys : M m t} -> {0 x : M n t} -> 
  {auto reqY : Extends y ys} -> 
  {auto prf0 : Like x (MS y ys)} ->
  Like x ys
likeSuccRight = %search
