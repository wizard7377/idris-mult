module Data.Grade.Util.Fin 
import Prelude
import Data.Grade.Logic
import Data.List.For
public export
interface Fin (t : Type) where
  1 elems : List t
  0 only : (x : t) -> For x elems

public export
Fin () where
  elems = [()]
  only () = %search
public export
Fin Bool where
  elems = [False, True]
  only False = Here
  only True = There Here
