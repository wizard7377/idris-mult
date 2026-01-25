module Prelude.Copy


import public Builtin
import Prelude
%default total
public export
interface Copy a where
  constructor MkCopy
  1 copy : 
    {0 b : a -> a -> Type} ->
    (1 x : a) -> 
    (1 f : (1 y : a) -> (1 z : a) -> b y z) -> 
    b x x
public export
copyWithEq : 
    forall a.
    {0 b : a -> a -> Type} ->
    (1 _ : Copy a) => 
    (1 x : a) ->
    (1 _ : ((1 y : a) -> (1 z : a) -> (0 prfY : y === x) => (0 prfZ : z === x) => b y z)) ->
    b x x

  
copyWithEq @{(MkCopy copy_inst)} x f = 
  let 
  1 g = copy_inst x f @{ %search } @{ %search }
  in g
  
public export
copy' : (1 _ : Copy a) => (1 _ : a) -> (1 _ : ((1 _ : a) -> (1 _ : a) -> b)) -> b
copy' @{(MkCopy copy_inst)} x f = copy_inst x f
public export
copyWithEq' : 
    (1 _ : Copy a) => 
    (1 x : a) ->
    (1 _ : (1 y : a) -> (1 z : a) -> (0 prfY : y === x) => (0 prfZ : z === x) => b) ->
    b
copyWithEq' @{(MkCopy copy_inst)} x f = copyWithEq @{MkCopy copy_inst} x (\y, z => f y z)
public export
Copy () where 
    copy () f = f () ()
    


export
infixr 0 |-
public export
(|-) : Type -> Type -> Type
hypo |- goal = {auto 0 prf : hypo} -> goal 
public export  
interface Drop a where
  constructor MkDrop
  drop : (1 x : a) -> Unit
  
  
export 
free : (1 prf : Drop a) => (1 _ : a) -> (1 _ : b) -> b
free @{(MkDrop drop_inst)} x y = case drop_inst x of 
  () => y
export 
free_eq : (0 _ : Drop a) => {0 x : a} -> (0 y : b) -> (Copy.free x y) === y
free_eq @{drop_inst} {x} y = ?free_eq_rhs
public export 
linear_absurd : (1 prf : Void) -> a
linear_absurd prf impossible

public export
SC : 
  {0 a : Type} -> 
  Copy a =>
  Drop a => --TODO: remove this constraint by changing how we clone'
  {0 p : a -> Type} ->
  {0 q : (x : a) -> p x -> Type} ->
  (1 f : ((1 x' : a) -> (1 y' : p x') -> q x' y')) ->
  (1 g : ((1 z' : a) -> p z')) ->
  (1 x : a) -> 
  (q x) (g x)
  
{-
SC f g x = let 
    1 [x0, x1] = x.clone' 2 @{ %search } @{CopyClone}
    0 prf_0 : (x === x0.val) = x0.prf
    0 prf_1 : (x === x1.val) = x1.prf
    1 i : p x = (rewrite prf_0 in g x0.val)
    1 h : (p x -@ q x (g x)) = rewrite prf_1 in f x1.val
    in h i

  

-}

public export
0 ECopy : forall a. Copy a
ECopy = MkCopy (\x, f => f x x)

public export
0 EDrop : forall a. Drop a
EDrop = MkDrop (\x => ())
