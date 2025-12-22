module Data.Grade.Form.Ops
import Data.Grade.Form.Types
import Data.Linear.Notation
import Data.Grade.Util.Linear
import Data.Linear.Interface
import Data.Grade.QNat
import Prelude.Num
import Builtin
import Prelude.Types
import Data.Linear.LMaybe
import Data.Grade.Logic
import Prelude
import Data.Rel
import Data.Vect
import Data.Fun
mutual 

    public export
    data Solve : Rel [Form, QNat] where 
        SolveTop : Solve FTop n 
        SolveVal : (m === n) |- Solve (FVal m) n
        SolveAdd : 
            {1 n1, n2 : QNat} -> 
            {auto 1 prf1 : Solve p n1} ->
            {auto 1 prf2 : Solve q n2} ->
            {auto 1 prf_eq : n1 + n2 === n} ->
            Solve (FAdd p q) n
        SolveMul : 
          {0 p, q : Form} ->
          {1 x : QNat} -> 
          {auto 1 prf_x : Solve p x} ->
          {auto 1 prf_n : SolveMany x q n} ->
          Solve (FMul p q) n
        SolveAltLeft : {auto 1 prf : Solve p n} -> Solve (FAlt p q) n
        SolveAltRight : {auto 1 prf : Solve q n} -> Solve (FAlt p q) n
          
    public export 
    data SolveMany : Rel [QNat, Form, QNat] where
      SolveSome : 
        {0 x : QNat} -> 
        {0 y : QNat} -> 
        {auto 1 prf1 : Solve p x} ->
        {auto 1 prf2 : SolveMany k p y} ->
        {auto 1 prf_eq : n === (x + y)} ->
        SolveMany (Succ k) p n
      SolveNone : 
        SolveMany Zero p n
    
  
mutual 
  public export
  Copy (Solve p n) where 
    copy f x = ?copy_rhs
    copy_eq = ?copy_eq_rhs
  public export
  Consumable (Solve p n) where 
    consume prf = ?consume_rhs
public export 
0 Unify : Rel [Form, Form]
Unify p q = (forall n. (Solve p n -@ Solve q n))

public export
record Equiv p q where
    constructor MkEquiv
    1 ltr : Unify p q
    1 rtl : Unify q p

public export 
data Path : Rel [Form, Form] where 
    Path_Refl : Path p p
    Path_Trans : Path p q -@ Path q r -@ Path p r
    Path_Top : Path p FTop
    Path_Bot : Path FBot p
    Path_Add_Comm : Path (FAdd p q) (FAdd q p)
    Path_Add_Both : Path p p' -@ Path q q' -@ Path (FAdd p q) (FAdd p' q')
    Path_Mul_Both : Path p p' -@ Path q q' -@ Path (FMul p q) (FMul p' q')
    

public export
infix 1 <:, :>, :~:, <?, ?>, #>, <#

%inline %tcinline public export
0 (<?) : Rel [QNat, Form]
x <? p = Solve p x
%inline %tcinline public export
0 (?>) : Rel [Form, QNat]
p ?> x = Solve p x
%inline %tcinline public export
0 (:~:) : Rel [Form, Form]
p :~: q = Equiv p q
%inline %tcinline public export
0 (<:) : Rel [Form, Form]
p <: q = Unify p q
%inline %tcinline public export
0 (:>) : Rel [Form, Form]
p :> q = Unify q p
%inline %tcinline public export
0 (#>) : Rel [Form, Form]
p #> q = Path p q
%inline %tcinline public export
0 (<#) : Rel [Form, Form]
p <# q = Path q p

    
