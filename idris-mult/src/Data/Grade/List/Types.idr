module Data.Grade.List.Types
import Relude
%default total
public export
data QList : Type -> Type where
  Nil  : QList a
  (::) : a -@ QList a -@ QList a
 
public export
Copy a => Copy (QList a) where 
    copy Nil f = f Nil Nil 
    copy (x :: xs) f = 
        copy xs (\xs1, xs2 => f (x :: xs1) (x :: xs2))
public export
QNil : QList a
QNil = Nil
public export
QCons : a -@ QList a -@ QList a
QCons x xs = x :: xs

