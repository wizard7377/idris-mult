module Data.Grade.Util.Types
import Builtin
import Prelude
 
%inline %tcinline
public export
LConst : (1 _ : b) -> ((_  : a) -> b)
LConst {a} x y = x
%inline %tcinline
public export
Const : (_ : b) -> ((_ : a) -> b)
Const {a} x y = x
 
%inline %tcinline
public export
LCompose : (1 f : (1 _ : a) -> b) -> (1 g : (1 _ : b) -> c) -> ((1 _ : a) -> c)
LCompose f g x = g (f x)

%inline %tcinline
public export
Compose : (f : a -> b) -> (g : b -> c) -> (a -> c)
Compose f g x = g (f x)

public export
interface Clone (0 t : Type) where 
    clone : (1 x : t) -> (LPair t t)
public export
interface Drop (0 t : Type) where 
    drop : (1 x : t) -> ()
  
  
public export 
0 lfst : (p : LPair t t) -> t
lfst (x # y) = x
public export 
0 lsnd : (p : LPair t t) -> t
lsnd (x # y) = y
public export
interface Clone t => LawfulClone (0 t : Type) where 
    prfCloneL : {0 x : t} -> (lfst (clone x)) === x
    prfCloneR : {0 x : t} -> (lsnd (clone x)) === x

