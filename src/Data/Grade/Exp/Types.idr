module Data.Grade.Exp.Types


import Data.Grade.Util.Relude
import Data.Grade.Mu.Ops
import Data.Grade.Form
import Data.Grade.Mu.Types
import Data.Grade.Omega.Types
import Decidable.Equality
import Data.Grade.Set
import Data.Linear.LVect
import Data.Grade.Mu.Lemma
import Prelude.Ops
import Data.Grade.Util.Linear
import Control.Function.FunExt
import Data.Grade.Util.Unique

%default total

%inline %tcinline
public export
0 A : {ty : Type} -> (p : ty -> Type) -> Type
A {ty} p = LExists {ty=ty} p
public export
0 AM : (n : QNat) -> (t : Type) -> Type
AM n t = A (Mu n t)
export 
infixl 1 ^^
public export
0 (^^) : (t : Type) -> (n : QNat) -> Type
(^^) t n = AM n t


{-
public export
0 AW : (p : (Qty -@ QNat)) -> (t : Type) -> Type
AW p t = A (Omega p t)
public export
infixl 1 ^
public export
0 (^) :  (t : Type) -> (p : (Qty -@ QNat))-> Type
(^) t p = AW p t
-}


export 
infixl 1 ^
||| The exponential type
||| This abstract over both the specific formula and the underlying witness, allowing for us to work with more "intuitive" values 
||| Because `Form` is a `Num`, type signatures like `String ^ 3` are perfectly valid 
public export
0 (^) :  (t : Type) -> (p : Form) -> Type
(^) t p = LExists (Omega p t)


export 
infix 9 ~?
||| The equality relation for existentials
public export
0 (~?) : LExists {ty} p -> LExists {ty} q -> Type
(LExists.LEvidence n x) ~? (LExists.LEvidence m y) = (n === m)
