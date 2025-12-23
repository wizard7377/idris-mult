module Data.Grade.Omega.Types
import Relude
import Data.Grade.List
import Data.Grade.Mu
  
public export
Form : Type 
Form = QList QNat
public export
0 Omega : (ns : Form) -> (t : Type) -> (w : t) -> Type
Omega ns t w = (1 n : QNat) -> ((0 prf : Elem n ns) => Mu n t w)

export 
infixl 5 |+|
export 
infixl 4 |*|
public export
(|+|) : Form -@ Form -@ Form
x |+| y = App2 ladd x y
public export
(|*|) : Form -@ Form -@ Form
x |*| y = App2 lmul x y
