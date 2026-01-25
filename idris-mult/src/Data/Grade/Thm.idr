module Data.Grade.Thm
import Data.Grade.Mu
import Data.Grade.Omega
import Data.Grade.Sigma
import Data.Grade.Exp
import Data.Grade.Logic 
import Relude
%hide Builtin.infixr.(#)
export
prefix 10 #
public export 
data (#) : QNat -> Type where 
  N1 : {0 n : QNat} -> (# (Succ n))
  NS : (# n) -@ (# (Succ n))
%inline %tcinline
public export 
type : Type -@ Type 
type a = a
export 
infixr 0 ->> 
public export 
(->>) : Type -> Type -> Type
(a ->> b) = a -@ b
export 
infix 0 <-> 
public export 
(<->) : Type -> Type -> Type
(a <-> b) = (a ->> b) :*: (b ->> a)

zero_is_void_ltr : (# 0) ->> Void
zero_is_void_ltr x impossible
zero_is_void_rtl : Void ->> (# 0)
zero_is_void_rtl v impossible 
zero_is_void : (# 0) <-> Void
zero_is_void = And zero_is_void_ltr zero_is_void_rtl

one_is_unit_ltr : (# 1) ->> Unit
one_is_unit_ltr N1 = ()

one_is_unit_rtl : Unit ->> (# 1)
one_is_unit_rtl () = N1

one_is_unit : (# 1) <-> Unit
one_is_unit = And one_is_unit_ltr one_is_unit_rtl
  
export  
mult_frac : (a' :/: a) :*: (b' :/: b) ->> (a' :*: b') :/: (a :*: b)
mult_frac (And f g) = \ (And x y) : (a :*: b) => And (f x) (g y)
export
cut_frac : (a :/: b) :*: (b :/: c) ->> (a :/: c)
cut_frac (And f g) = \ x => f (g x)
export
inverse_frac : (# 1) <-> (Quest (a :/: a))
||| (a' / a) + (b' / b) ->> ((a' * b) + (a * b')) / (a * b)
cross_frac : (a' :/: a) :+: (b' :/: b) ->> ((a' :*: b) :+: (a :*: b')) :/: (a :*: b)
cross_frac (Par f) (And x y) = Par (\case 
    InL z' => f $ InL $ \z'' => (let 
        1 p = z'' x 
        1 q = And p y
        in z' q)
    InR z' => f $ InR $ \z'' => (let 
        1 p = z'' y
        1 q = And x p
        in z' q)
  )
distrib_exp : (a :*: b) :^: n <-> (a :^: n) :*: (b :^: n)
distrib_exp = Exp.push `And` Exp.pull
distrib_exp_frac : (a :/: b) :^: n ->> (a :^: n) :/: (b :^: n)
distrib_exp_frac = Exp.app  
distr_prod : ((a :+: b) :*: c) ->> ((a :*: c) :+: (b :*: c))
distr_prod (And x y) = Par (\case 
    InL f => f (And (get_left x) y)
    InR f => f (And (get_right x) y)
  )

square_prod : (a :^: 2) ->> (a :*: a)
square_prod x = let 
  1 (And y z) = Exp.split x
  1 y' = Exp.extract y
  1 z' = Exp.extract z
  in And y' z'

anti_distr_prod1 : ((a :*: c) :+: (b :*: c)) ->> ((a |+| b) :*: c)
anti_distr_prod1 (Par f) = let 
  (And x z) = f $ InL id
  in And (InL x) z
anti_distr_prod2 : ((a :*: c) :+: (b :*: c)) ->> ((a |+| b) :*: c)
anti_distr_prod2 (Par f) = let 
  (And x z) = f $ InR id
  in And (InR x) z
