module Data.Grade.Logic
import Relude 
import public Data.Grade.Sigma
||| Contractible types 
public export
record Contractible (0 a : Type) where 
    constructor Contract
    1 center' : a
    0 deform : {x : a} -> (x = center')

public export
contract : {0 a : Type} -> (1 x : a) => (0 prf : {0 y : a} -> (y === x) ) => Contractible a
contract @{x} @{prf} = Contract x prf
public export
(.center) : Contractible a -@ a
(.center) (Contract c d) = c

public export
Point : (1 _ : Contractible a) => a
Point @{c} = c.center

public export
data QDec : Type -> Type where
    QYes : a -@ QDec a
    QNo : (a -@ Void) -@ QDec a

public export
interface QDecEq (0 t : Type) where 
  %hint
  1 qDecEq : {1 x, y : t} -> QDec (x === y)

public export
QNot : (t : Type) -> Type
QNot t = (t -@ Void)

public export
MkNot : QNot t -@ Not t
MkNot f x = f x
public export
efalse : forall t. (0 prf : Void) -> t
efalse prf impossible 
public export
scandel : (0 prf : x = y) -> (x = y)
scandel prf = rewrite prf in Refl

public export
decScandel : (0 prf : Dec (x = y)) -> Dec (x === y)
decScandel = believe_me ()
export
infixr 2 <&> </>
public export
data (<&>) : Type -> Type -> Type where
  And : (1 fst : a) -> (1 snd : b) -> a <&> b
public export
data (</>) : Type -> Type -> Type where
  InL : (1 left : a) -> a </> b
  InR : (1 right : b) -> a </> b
