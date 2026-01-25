module Data.Grade.Omega

import Relude
import Data.Grade.Logic
import Data.Grade.Form
import Data.Grade.Mu
public export
data Omega : (n : CNat) -> (t : Type) -> (w : t) -> Type where 
  WF : Mu n t w -@ Omega (Fin n) t w
  WI : t -@ Inf (Omega ∞ t w) -@ Omega ∞ t w

export 
get_value : IsFinite n => CNat -@ QNat
get_value @{prf} (Fin n) = n
get_value @{prf} ∞ = ?h00432432
%hint export 
unwrap_fin : (prf : IsFinite n) => Omega n t w -@ Mu (get_value @{prf} n) t w
unwrap_fin @{prf} (WF x) = ?h03443243
%hint export 
contract_omega : (w : t) => Contractible (Omega n t w) 
contract_omega @{w} = ?h10
private  
contract_omega_fin : (w : t) => Contractible (Omega (Fin n) t w)
contract_omega_fin @{w} = ?h11
private 
h_ex : (w : t) -> Omega ∞ t w
h_ex w = WI w (Delay (h_ex w))
private
contract_omega_inf : (w : t) => Contractible (Omega ∞ t w)
contract_omega_inf @{w} = Contract (h_ex w) ?h_prf
private %hint 
0 not_zero_succ : (1 n : QNat) -> (Fin (Succ n) = 0) -> Void
not_zero_succ n Refl impossible
public export
Yield : {1 n : CNat} -> (1 x : Omega (CSucc n) t w) -> (t :*: Omega n t w)
Yield {n=(Fin n')} (WF x) = let 
    1 (MS y ys) = x 
  in n' >>> And y (WF ys)
Yield {n=∞} (WI x xs) = And x xs
public export
WZ : Omega (Fin Zero) t w
WZ = WF MZ
public export 
WS : (1 w : t) -> (1 x : Omega n t w) -> Omega (CSucc n) t w
WS w (WF x) = WF (MS w x)
WS w (WI x xs) = WI x $ WS w xs
public export 
WS' : (1 w : t) -> (0 prf : w === w') => (1 x : Omega n t w') -> Omega (CSucc n) t w
WS' x @{Refl} xs = WS x xs
public export 
map : (f : t -@ u) -> Omega n t w -@ Omega n u (f w)
map f (WF x) = WF (map f x)
map f (WI x xs) = WI (f x) $ map f xs

public export
app : Omega n (t -@ u) w_f -@ Omega n t w_x -@ Omega n u (w_f w_x)
app (WF f) (WF x) = WF (app f x)
app (WI f fs) (WI x xs) = WI (f x) $ app fs xs
 
public export
split_inf_inf : Omega ∞ t w -@ Omega ∞ t w :*: Omega ∞ t w 
split_inf_inf (WI x (WI y ys)) = let 
    1 (And z zs) = assert_total (split_inf_inf ys)
    in And (WI x z) (WI y zs)
public export 
split_inf : {1 q : CNat} -> Omega ∞ t w -@ Omega ∞ t w :*: Omega q t w
split_inf {q=Fin 0} x = And x (WF MZ)
split_inf {q=Fin (Succ q')} (WI x xs) = let 
    1 (And y ys) = assert_total (split_inf xs)
    in And (WI x y) ys
split_inf {q=∞} (WI x xs) = split_inf_inf (WI x xs) 

public export
split : {1 p, q : CNat} -> Omega (p + q) t w -@ Omega p t w :*: Omega q t w
 
combine_inf : Omega ∞ t w -@ Omega ∞ t w -@ Omega ∞ t w
combine_inf (WI x xs) ys = WI x $ combine_inf xs ys
private 
combine_inf2 : (1 w : t) -> Omega ∞ t w -@ Omega ∞ t w
combine_inf2 w (WI x xs) = WI x $ combine_inf2 w xs

public export
combine : {0 m, n : CNat} -> Omega m t w -@ Omega n t w -@ Omega (m + n) t w
combine {m = Fin m'} {n = Fin n'} (WF x) (WF y) = WF (Mu.combine x y)
combine {m = ∞ } {n = Fin n'} (WI x xs) (WF y) = let 
    1 ys = Omega.combine (WF y) xs
    0 prf : free (Fin n') ∞ === ∞ = free_eq ?
    1 ys' : Inf (Omega ∞ t w) = rewrite sym prf in ys
    0 prf' : cadd ∞ (Fin n') === ∞ = %search
  in assert_total $ rewrite prf' in WI x ys'
combine {m = Fin m'} {n = ∞} (WF x) (WI y ys) = let 
    1 xs = combine ys (WF x)
    0 prf : free (Fin m') ∞ === ∞ = free_eq ?
    1 xs' : Inf (Omega ∞ t w) = rewrite sym prf in xs
    0 prf' : cadd (Fin m') ∞ === ∞ = %search
  in assert_total $ rewrite prf' in WI y xs'
combine {m = ∞} {n = ∞} (WI x xs) (WI y ys) = let 
  0 prf : ∞ + ∞ === ∞ = free_eq ? 
  in rewrite prf in combine_inf (WI x xs) (WI y ys)
private 
brush_off : Omega p t w -@ Omega ∞ t w -@ Omega ∞ t w
brush_off x y = rewrite sym $ cadd_infinite_right ? in combine x y
public export
lift : Mu n t w -@ Omega (Fin n) t w
lift x = WF x
public export
lower : Omega (Fin n) t w -@ Mu n t w
lower (WF x) = x 
 
private 
join_mu : Mu n (Omega p t w) w' -@ Omega (Fin n * p) t w
join_mu MZ = let 
    0 prf : 0 * p === 0 = cmul_zero_left ?
  in rewrite prf in WZ
join_mu {n=Succ n'} (MS x xs) = let 
  1 ys : Omega (Fin n' * p) t w = join_mu xs
  1 z : Omega (Fin (Succ n') * p) t w = rewrite cmul_succ_left (Fin n') p in combine x ys
  in z

mutual  
    ||| Public wrapper of join_
    public export 
    join : {1 n : CNat} -> {0 w' : Omega n t w} -> Omega m (Omega n t w) w' -@ Omega (m * n) t w
    join {n} = assert_total join 
    covering private
    join_ : {1 n : CNat} -> {0 w' : Omega n t w} -> Omega m (Omega n t w) w' -@ Omega (m * n) t w

    join_ {m = (Fin m')} {n = Fin n'} (WF x) = n' >>> rewrite sym $ lift_mul m' n' in WF (Mu.join $ Mu.map lower x)

    join_ {m = ∞} {n = ∞} (WI x xs) = let 
        0 prf : cmul ∞ ∞ === ∞ = %search
        1 ys : Omega ∞ t w = rewrite sym prf in Omega.join (assert_smaller (WI x xs) xs)
        0 prf' : free ∞ ∞ === ∞ = free_eq ?
        in rewrite prf in rewrite sym prf' in combine x ys

    join_ {m = ∞} {n = (Fin Zero)} (WI x xs) = let 
    1 y : Omega 0 t w = x
    1 ys : Omega 0 t w = rewrite sym $ cmul_zero_right ∞ in join xs
    1 z : Omega 0 t w = combine y ys
        in rewrite cmul_zero_right ∞ in z

    join_ {m = ∞} {n = (Fin (Succ n'))} (WI x xs) = 
        let 
        1 y : Omega (Fin (Succ n')) t w = x
        1 ys : Omega ∞ t w = rewrite sym $ cmul_infinite_nonzero_left (Fin $ Succ n') @{ not_zero_succ $ n' } in join_ xs
        1 z : Omega ∞ t w = rewrite sym $ free_eq ∞ in combine y ys
        in rewrite cmul_infinite_nonzero_left (Fin $ Succ n') @{ not_zero_succ $ n' } in z

    join_ {m = (Fin Zero)} {n = ∞} (WF MZ) = rewrite cmul_zero_left ∞ in WZ

    join_ {m = (Fin (Succ m'))} {n = ∞} (WF (MS y ys)) = let 
        1 zs : Omega (Fin m' * ∞) t w = join (WF ys)
        0 prf : free (Fin m' * ∞) ∞ === ∞ = free_eq ?
        1 r : Omega ∞ t w = rewrite sym prf in combine y zs

        in rewrite cmul_infinite_nonzero_right (Fin $ Succ m') @{ not_zero_succ $ m' } in r

public export 
expand : {1 m, n : CNat} -> Omega (m * n) t w -@ Omega m (Omega n t w) Point
expand {m = Fin m'} {n = Fin n'} x = let 
  1 x' : Omega (Fin (m' * n')) t w = x
  in ?h0
expand {m = ∞} {n = ∞} x = let 
  0 prf : free ∞ ∞ === ∞ = %search
  1 And y ys = Omega.split {p=Infinite} {q=Infinite} x
  in WI y $  (Omega.expand (rewrite prf in ys))
expand {m = ∞} {n = (Fin n')} x = ?h1 
expand {m = (Fin m')} {n = ∞} x = ?h2
public export 

react :
  {1 n0, n1, n2 : CNat} -> 
  {0 t, u : Type} -> 
  {0 w_t : t} -> 
  {0 w_u : u} -> 
  {0 w_f : Omega n1 t w_t -@ Omega n2 u w_u} ->
  Omega n0 (Omega n1 t w_t -@ Omega n2 u w_u) w_f -@
  Omega (n0 * n1) t w_t -@
  Omega (n0 * n2) u w_u
react {n0, n1} f x = join $ app f $ expand x 

