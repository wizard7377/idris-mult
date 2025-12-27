module Data.Grade.List
import Relude
import Data.Grade.Logic

%default total
public export
data QList : Type -> Type where
  Nil  : QList a
  (::) : a -@ QList a -@ QList a
 
public export
Copy a => Copy (QList a) where 
    copy Nil f = f Nil Nil 
    copy (x :: xs) f = 
        copy xs (\xs1, xs2 => copy x (\x1, x2 => f (x1 :: xs1) (x2 :: xs2)))
public export
QNil : QList a
QNil = Nil
public export
QCons : a -@ QList a -@ QList a
QCons x xs = x :: xs

public export
data Any : (a -> Type) -> QList a -> Type where
  Because  : p x -@ Any p (QCons x xs)
  However : Any p xs -@ Any p (QCons x xs)

public export
data All : (a -> Type) -> QList a -> Type where
  Done : All p Nil 
  Also : p x -@ All p xs -@ All p (x :: xs)

public export 
data IsElem : a -> QList a -> Type where
  Here : IsElem x (x :: xs)
  There : IsElem x xs -@ IsElem x (y :: xs)
export
ElemAny : IsElem x xs -> Any (\y => x = y) xs

export 
AnyElem : Any (\y => x = y) xs -> IsElem x xs
public export
Each : {a : Type} -> QList a -> QList a -> Type
Each x y = {p : a -> Type} -> Any p x -> Any p y
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
    1 [x0, x1] = x.clone 1
    1 [xs0, xs1] = xs.clone 1
    1 y0 = f x0.val
    1 ys0 = App fs xs0.val
    1 y1 = Map f xs1.val
    1 ys1 = App fs (Pure x1.val)
    in Concat (y0 :: ys0) (Concat y1 ys1) 

public export
0 Map' : (a -@ b) -@ QList a -@ QList b
Map' f Nil = Nil
Map' f (x :: xs) = f x :: Map' f xs
public export
0 App' : QList (a -@ b) -@ (QList a -@ QList b)
App' [] _ = []
App' _ [] = []
App' (f :: fs) (x :: xs) = Concat ((f x) :: (Map f xs)) (Concat (App' fs (Pure x)) (App' fs xs))

export 
App2 : Drop a => Copy a => Drop b => Copy b => (a -@ b -@ c) -> (QList a -@ QList b -@ QList c)
App2 f [] x = drop x `seq` []
App2 f xs [] = drop xs `seq` []  
App2 f (x :: xs) (y :: ys) = let 
    1 [x0, x1] = x.clone 1
    1 [xs0, xs1] = xs.clone 1
    1 [y0, y1] = y.clone 1
    1 [ys0, ys1] = ys.clone 1
    1 z0 = f x0.val y0.val
    1 zs0 = App2 f xs1.val (Pure y1.val)
    1 z1 = App2 f (Pure x1.val) ys1.val
    1 zs1 = App2 f xs0.val ys0.val
    in assert_total $ Concat (z0 :: zs0) (Concat z1 zs1)
public export
0 App2' : (a -@ b -@ c) -@ (QList a -@ QList b -@ QList c)
App2' f [] _ = []
App2' f _ [] = []
App2' f (x :: xs) (y :: ys) = let
    1 z0 = f x y
    1 zs0 = Map (f x) ys
    1 z1 = App2' f xs (Pure y)
    1 zs1 = App2' f xs ys
    in Concat (z0 :: zs0) (Concat z1 zs1)
  
export 
0 App2_rep : (((App2 @{ EDrop } @{ ECopy } @{ EDrop } @{ ECopy } f xs ys) === App2' f xs ys))
App2_rep = ?app2_rep_rhs
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

