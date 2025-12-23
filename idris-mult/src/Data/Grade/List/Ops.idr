module Data.Grade.List.Ops
import Data.Grade.List.Types
import Data.Linear.Notation
import Relude
public export
data Any : (a -> Type) -> QList a -> Type where
  Here  : p x -@ Any p (QCons x xs)
  There : Any p xs -@ Any p (QCons x xs)

public export
data All : (a -> Type) -> QList a -> Type where
  Done : All p Nil 
  Also : p x -@ All p xs -@ All p (x :: xs)

public export 
Elem : a -> QList a -> Type
Elem x l = Any (\y => x === y) l
public export
Drop a => Drop (QList a) where
  drop Nil = ()
  drop (x :: xs) = drop x `seq` drop xs
 
       
public export
Concat : QList a -@ QList a -@ QList a
Concat Nil ys = ys
Concat (x :: xs) ys = x :: Concat xs ys 
public export
Map : (a -@ b) -> QList a -@ QList b
Map f Nil = Nil
Map f (x :: xs) = f x :: Map f xs

public export
Join : QList (QList a) -@ QList a
Join Nil = Nil
Join (xs :: xss) = Concat xs (Join xss)
public export
Pure : a -@ QList a
Pure x = x :: Nil
public export
App : Drop a => Copy a => QList (a -@ b) -> (QList a -@ QList b)
App _ [] = []
App [] x = drop x `seq` []
App (f :: fs) (x :: xs) = let 
    1 [x0, x1] = x.clone @{CopyClone} 1
    1 [xs0, xs1] = xs.clone @{CopyClone} 1
    1 y = f $$ x0
    1 ys = App fs $$ xs0
    1 ys0 = Map f $$ xs0
    1 ys1 = App fs (Pure $$ x1)
    in y :: (Concat ys $ Concat ys0 ys1)

public export
App2 : (a -@ b -@ c) -> QList a -@ QList b -@ QList c
App2 f xs ys = ?app2_help
public export
(<$>) : (a -@ b) -> QList a -@ QList b
f <$> xs = Map f xs

public export
(<*>) : Copy a => Drop a => QList (a -@ b) -> (QList a -@ QList b)
fs <*> xs = App fs xs
  
public export
pure : a -@ QList a
pure x = [x]
public export
Num (QList QNat) where 
  fromInteger x = [fromInteger x]
  (+) xs ys = ?add_list
  (*) xs ys = ?mul_list
