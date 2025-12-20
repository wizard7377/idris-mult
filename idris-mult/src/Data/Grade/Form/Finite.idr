module Data.Grade.Form.Finite 
import Prelude
import Data.Grade.Logic
import Data.List.Elem
import Data.Grade.QNat.Types
import Data.Grade.QNat.QFin
public export
interface Finite (t : Type) where
  constructor MkFinite
  elems : List t
  0 only : (x : t) -> Elem x elems

public export
Finite () where
  elems = [()]
  only () = %search
public export
Finite Bool where
  elems = [False, True]
  only False = Here
  only True = There Here

private 
Finite (QFin Zero) where
  elems = [(Elem Zero LLTE_Z)]
  only (Elem Zero LLTE_Z) = Here
private 
{hi : QNat} -> Finite (QFin hi) => Finite (QFin (Succ hi)) where
  elems = ?h0
  only = ?h1
