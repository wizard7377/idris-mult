module Data.Grade.Form.Sugar 


import Data.Grade.Form.Types
import Data.Grade.Form.Ops
import Relude 
import Prelude.Interfaces
import Data.Grade.Logic

%default total
public export
interface Formula f where 
    constructor MkFormula
    1 formula : f -@ Form

public export
Formula QNat where 
    formula n = FVal [n] 

public export
Formula Integer where 
    formula n = assert_linear (\n' => FVal [fromInteger n']) n
 
public export
unQList : List a -@ QList a
unQList [] = []
unQList (x :: xs) = x :: unQList xs
public export
Formula (List Integer) where 
    formula ns = assert_linear (\ns' => FVal (unQList $ Prelude.Interfaces.map fromInteger ns')) (ns)
public export
Formula Form where 
    formula f = f
public export 
Formula t => Formula (Form -@ t) where 
    formula f = formula $ f FVar
 
public export 
Formula t => Formula (Form -> t) where 
    formula f = formula $ f FVar
public export 
Formula () where 
    formula () = FVar 
 
export 
infixl 4 |+| 
export
infixl 5 |*|
export
infixl 3 |^|, |-|

public export
(|+|) : Formula f1 => Formula f2 => f1 -@ f2 -@ Form
(|+|) f1 f2 = FAdd (formula f1) (formula f2)
public export
(|*|) : Formula f1 => Formula f2 => f1 -@ f2 -@ Form
(|*|) f1 f2 = FMul (formula f1) (formula f2)

export
infix 9 :~, :>, <:, :? 
public export
0 (:~) : Formula f1 => Formula f2 => f1 -@ f2 -@ Type
(:~) f1 f2 = Equiv (formula f1) (formula f2)
public export
0 (:>) : Formula f1 => Formula f2 => f1 -@ f2 -@ Type
(:>) f1 f2 = Unify (formula f1) (formula f2)
public export
0 (<:) : Formula f1 => Formula f2 => f1 -@ f2 -@ Type
(<:) f1 f2 = Unify (formula f2) (formula f1)
public export
0 (:?) : Formula f1 => Formula f2 => f1 -@ QNat -@ Type
(:?) f1 f2 = Solve (formula f1) f2
