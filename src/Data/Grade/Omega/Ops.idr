module Data.Grade.Omega.Ops


import Data.Grade.Util.Relude
import Data.Grade.Mu.Ops
import Data.Grade.Mu
import Data.Grade.Form
import Data.Grade.Omega.Types
import Decidable.Equality
import Data.Grade.Set
import Data.Linear.LVect
import Data.Grade.Mu.Lemma
import Prelude.Ops
import Data.Grade.Util.Linear
import Control.Function.FunExt
import Data.Grade.Util.Unique
import Data.Grade.Form.Sugar
import Prelude.Types
-- %default total

Omega_0_1 : Omega [] t w -@ Omega [FVal [1]] t w
Omega_0_1 (Omega0 f) = OmegaVal ?omega0_1
  where 
    1 go : (1 n : QNat) -> (0 prf : QElem n [1]) => Mu n t w

{-
public export
flatten : {1 p : QList Form} -> Omega p t w -@ (Exists Form (\q => Omega [q] t w))
flatten {p=Nil} (Omega0 f) = let 

  1 go : Omega [FVal [1]] t w = OmegaVal ?flatten_omega0
  in Given (FVal [1]) go
  
flatten {p=(q :: Nil)} f = seq q $ Given q f
flatten {p=(p :: q :: r)} f = let 
    1 f' : Omega ((p |*| q) :: r) t w = Join f
    in assert_total $ flatten {p=((p |*| q) :: r)} f'
mutual 
    public export 
    Omega2_to_Omega1 : Omega2 p' q' t w -@ Omega1 p' (Omega1 q' t w) w'
    Omega2_to_Omega1 (OmegaVal2 v) = fix_later (OmegaVal1 v)
    Omega2_to_Omega1 (OmegaVar2 v) = let 
        1 go : ((1 p : Form) -> Omega1 p _ _) = \p => Omega2_to_Omega1 (v p)
        in OmegaVar1 (Delay go)
    Omega2_to_Omega1 (Combine2 f g) = let 
        1 f' : Omega1 _ (Omega1 q' t w) w' = Omega2_to_Omega1 f
        1 g' : Omega1 _ (Omega1 q' t w) w' = Omega2_to_Omega1 g
        in Combine1 f' g'
    Omega2_to_Omega1 (Join2 f) = let 
        1 f' : Omega1 _ (Omega1 _ t w) _ = Omega2_to_Omega1 f
        1 (Join1 f'') = f'
        in ?omega_mul_join 

    public export
    expand : Omega1 (p |*| q) t w -@ Omega1 p (Omega1 q t w) _
    expand (Join1 f) = Omega2_to_Omega1 f
public export
combine1' : Omega1' p t w -@ Omega1' q t w -@ Omega1' (p |+| q) t w
combine1' f g @{(For (For x y) (Elem (For prf_x prf_y) prf_sum))} n = let 
    1 y_f : Mu x t w = f @{prf_x} x
    1 y_g : Mu y t w = g @{prf_y} y
    1 y_sum : Mu (ladd x y) t w = Mu.combine y_f y_g
    1 y_sum' : Mu n t w = rewrite prf_sum in y_sum
    in seq n $ y_sum'
  
public export
combine : Omega (p :: r) t w -@ Omega (q :: r) t w -@ Omega ((p |+| q) :: r) t w
combine f g = Combine f g

public export
combine1 : Omega1 p t w -@ Omega1 q t w -@ Omega1 (p |+| q) t w
combine1 f g = Combine1 f g

public export
join' : Omega1 q (Omega1' p t w) _ -@ Omega1 (p |*| q) t w
join' f = ?join_omega

public export
split : Omega1 (p |+| q) t w -@ (Duple (Omega1 p t w) (Omega1 q t w))
split (Combine1 f g) = For f g

mutual
    public export
    app1 : Omega1 p (t -@ u) wf -@ Omega1 p t wx -@ Omega1 p u (wf wx)
    app1 (OmegaVal1 mf) (OmegaVal1 mx) = OmegaVal1 ?h0
    app1 (OmegaVar1 f) (OmegaVar1 x) = OmegaVar1 (go (OmegaVar1 f) (OmegaVar1 x))
        where 
            go : (Omega1 FVar (t -@ u) wf) -@ (Omega1 FVar t wx) -@ ((1 p : Form) -> Omega1 p u (wf wx))
            go (OmegaVar1 mf) (OmegaVar1 mx) n = let 
                [n0, n1] = n.clone 2 @{ %search } @{CopyClone}
                in app1 (mf $$ n0) (mx $$ n1)
    app1 (Combine1 f1 f2) (Combine1 x1 x2) = combine1 (app1 f1 x1) (app1 f2 x2)
    app1 (Join1 f') (Join1 x') = ?omega_mul
    app1_2 : Omega1 p (a -@ b -@ c) wf -@ Omega1 p a wx -@ Omega1 p b wy -@ Omega1 p c (wf wx wy)
    app1_2 f x y = app1 (app1 f x) y
public export
map1 : {1 p : Form} -> (f : t -@ u) -> Omega1 p t w -@ Omega1 p u (f w)
map1 f x = app1 (genW1 f) x

public export
forget1 : Omega1 p t w -@ Omega1' p t w
forget1 (OmegaVal1 mv) @{prf} n = seq prf $ mv @{prf} n 
forget1 (OmegaVar1 mv) @{prf} n = let 
  [n0, n1] = n.clone 2 
  mv' : Omega1' (FVal [n0.val]) t w = assert_total (forget1 (mv $ FVal [n0.val]))
  0 prf' : (n1.val === n0.val) = ?cloneEq
  1 prf'' : Solve (FVal [n0.val]) n1.val = HintEq @{prf'}
  1 r = mv' @{prf''} n1.val
  1 r' : Mu n t w = rewrite n1.prf in r
  in r'
forget1 (Combine1 f g) @{prf} n = let 
    1 f' : Omega1' _ t w = forget1 f 
    1 g' : Omega1' _ t w = forget1 g 
    in combine1' f' g' @{prf} n
forget1 (Join1 f) @{prf} n = ?forget1_join1_omega -- assert_total $ forget1 (join1' f) @{prf} n
-- TODO: prove totality
  
mutual 
    public export
    weaken1 : Omega1 p t w -@ ((0 prf : Unify p q) => Omega1 q t w)
    weaken1 f @{prf} = case f of
        OmegaVal1 mv => ?weaken1_omega_val
        OmegaVar1 mv => ?weaken1_omega_var
        Combine1 f1 f2 => ?weaken1_omega_add
        Join1 f' => ?weaken1_omega_mul


namespace Notation
  public export
  pure : (1 w : t) -> Omega1 (FVal [1]) t w
  pure w = ?pure_omega 
  public export
  (<$>) : {1 p : Form} -> (f : t -@ u) -> Omega1 p t w -@ Omega1 p u (f w)
  (<$>) = map1
  public export
  (<*>) : Omega1 p (t -@ u) wf -@ Omega1 p t wx -@ Omega1 p u (wf wx)
  (<*>) = app1
-}
