module Data.Grade.Util.Finite 
import Prelude
import Data.Grade.Logic
import Data.List.Elem
public export
interface Finite (t : Type) where
  1 elems : List t
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
