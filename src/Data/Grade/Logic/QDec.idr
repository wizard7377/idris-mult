module Data.Grade.Logic.QDec  
import public Data.Linear.Notation
import Builtin
import Prelude
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
