module Data.Grade.Logic.QList
import Relude
public export
data QList : Type -> Type where
  Nil : QList a
  (::) : (1 x : a) -> (1 xs : QList a) -> QList a
  
public export
data QElem : (1 x : a) -> (1 xs : QList a) -> Type where
  QHere : (prf : y === x) => QElem y (x :: xs)
  QThere : QElem x xs -> QElem x (y :: xs)

%hint 
export 
QElemRefl : (0 x : a) -> (0 y : a) -> QElem x (y :: []) => x === y
QElemRefl x y @{QHere @{prf}} = prf
%hint 
export 
HintEq : (0 _ : x === y) => QElem x (y :: ys)   
HintEq @{prf} = rewrite prf in QHere
  
  
public export
Uninhabited (QElem x Nil) where 
    uninhabited prf = case prf of {}

public export
Consumable a => Consumable (QList a) where 
    consume Nil = ()
    consume (x :: xs) = seq x (consume xs)
public export
Copy a => Copy (QList a) where 
    copy f Nil = f Nil Nil
    copy f (x :: xs) = copy (\x, y => copy (\xs, ys => f (x :: xs) (y :: ys)) xs) x
    copy_eq = ?copy_qlist_eq

public export
Consumable (QElem x xs) where 
    consume (QHere) = ()
    consume (QThere prf) = consume prf

public export
QConcat : QList a -@ QList a -@ QList a
QConcat Nil ys = ys
QConcat (x :: xs) ys = x :: (QConcat xs ys)
public export
QMap : (a -@ b) -> (QList a -@ QList b)
QMap f Nil = Nil
QMap f (x :: xs) = (f x) :: (QMap f xs)
  
public export
QApp : Copy a => Consumable a => QList (a -@ b) -> (QList a -@ QList b)
QApp Nil ys = seq ys Nil
QApp (f :: fs) xs = let 
  1 [x0, x1] = xs.clone @{CopyClone} 1 
  in (QMap f x0.val) `QConcat` (QApp fs x1.val)
