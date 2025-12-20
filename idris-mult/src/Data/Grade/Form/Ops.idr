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
data Path : Nat -> Rel [Form, Form] where 
    ||| A path of length zero between two identical formulas
    LoopStep : p === q |- Path 1 p q
    ||| Transititivity of paths
    JoinStep : Path len0 p q =@ Path len1 q r =@ Path (len0 + len1) p r
    ||| (P ~> Q), R |- (P * R ~> (P * Q))
    MultStep : Path len0 p p' =@ Path len1 q q' =@ Path (len0 + len1) (FMul p q) (FMul p' q')
    ||| (P ~> Q), R |- (P + R ~> (P + Q))
    AddStep : Path len0 p p' =@ Path len1 q q' =@ Path (len0 + len1) (FAdd p q) (FAdd p' q')
    

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
p #> q = (Exists Nat (\len => Path len p q))
%inline %tcinline public export
0 (<#) : Rel [Form, Form]
p <# q = (Exists Nat (\len => Path len q p))

    
