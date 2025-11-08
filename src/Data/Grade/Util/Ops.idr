module Data.Grade.Util.Ops
export  
infixr 0 ==>
public export 
0 (==>) : Type -> Type -> Type
a ==> b = (0 prf : a) => b
