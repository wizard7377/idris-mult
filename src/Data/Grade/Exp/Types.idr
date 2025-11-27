module Data.Grade.Exp.Types


import Data.Grade.Util.Relude
import Data.Grade.Mu.Ops
import Data.Grade.Form
import Data.Grade.Form.Sugar
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
import public Data.Grade.Form.Sugar
%default total

%inline %tcinline
public export
0 A : {ty : Type} -> (p : ty -> Type) -> Type
A {ty} p = Exists ty p
public export
0 AM : (n : QNat) -> (t : Type) -> Type
AM n t = A (Mu n t)
export 
infixl 1 ^^
public export
0 (^^) : (t : Type) -> (n : QNat) -> Type
(^^) t n = (w : t) #? (Mu n t w)


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

public export 
0 Exp : (t : Type) -> (p : Form) -> Type
Exp t p = (w : t) #? (Omega p t w)
export 
infixl 1 ^
||| The exponential type
||| This abstract over both the specific formula and the underlying witness, allowing for us to work with more "intuitive" values 
||| Because `Form` is a `Num`, type signatures like `String ^ 3` are perfectly valid 
public export
0 (^) : Formula f => (t : Type) -> (p : f) -> Type
(t ^ p) = Exp t (formula p)


export 
infix 9 ~?
||| The equality relation for existentials
public export
0 (~~) : Exists ty p -> Exists ty q -> Type
(Given n x) ~~ (Given m y) = (n === m)
