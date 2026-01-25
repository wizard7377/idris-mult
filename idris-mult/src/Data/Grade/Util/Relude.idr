module Data.Grade.Util.Relude

import public Builtin
import public Prelude.Basics
import public Prelude.Cast
import public Data.Grade.QNat
import public Data.Nat
import public Data.Linear.Notation
import public Data.Linear.Interface
import public Data.Linear.LEither
import public Prelude.Num
import public Prelude.Ops
import public Prelude.Types
import public Prelude.Uninhabited
import public Data.Grade.Util.Ops

%inline %tcinline
public export %unsafe
trust_me : a -@ b
trust_me x = prim__believe_me a b x
%inline %tcinline
public export %unsafe
axiom : a
axiom = prim__believe_me () a ()

public export
($|) : ((a -> b) -@ c) -@ b -@ c
($|) f x = f (\_ => x)
export
infixl 9 $|

%unsafe 
public export
fix_later : {0 a, b : Type} -> a -@ b
fix_later {a,b} x = prim__believe_me a b x

infixr 0 =@
public export
(=@) : Type -> Type -> Type
(=@) a b = (1 _ : a) => b
export
infixr 0 >>>
public export
(>>>) : Drop a => a -@ b -@ b
x >>> y = drop x `seq` y
  
public export
Drop (a === b) where 
  drop Refl = ()

-- infixr 0 ->@  
export
typebind infixr 0 ->@
%inline %tcinline
public export 
0 (->@) : (a : Type) -> (a -> Type) -> Type
(->@) a b = (1 x : a) -> b x
export
typebind infixr 0 =>@
%inline %tcinline
public export 
0 (=>@) : (a : Type) -> (a -> Type) -> Type
(=>@) a b = (1 x : a) => b x
export
typebind infixr 0 ->?
%inline %tcinline
public export 
0 (->?) : (a : Type) -> (a -> Type) -> Type
(->?) a b = (0 x : a) -> b x
export
typebind infixr 0 =>?
%inline %tcinline
public export 
0 (=>?) : (a : Type) -> (a -> Type) -> Type
(=>?) a b = (0 x : a) => b x
