module Data.Grade.Cat
import Relude
%hide Data.Linear.Interface.counit
public export
interface Isomorphic (0 a : Type) (0 b : Type) where
  1 ltr : a -@ b
  1 rtl : b -@ a
  0 rtl_ltr_id : {0 x : a} -> rtl (ltr x) === x
  0 ltr_rtl_id : {0 y : b} -> ltr (rtl y) === y
public export
(prf : Equal a b) => Isomorphic a b where
  ltr x = rewrite sym prf in x
  rtl y = rewrite prf in y
  ltr_rtl_id = Refl
  rtl_ltr_id = Refl
public export
Isomorphic a b => Isomorphic b a where
  ltr = rtl
  rtl = ltr
  ltr_rtl_id = rtl_ltr_id
  rtl_ltr_id = ltr_rtl_id
public export
(prfAB : Isomorphic a b) => (prfBC : Isomorphic b c) => Isomorphic a c where
  ltr x = ltr @{prfBC} $ ltr x
  rtl y = rtl @{prfAB} $ rtl y
  ltr_rtl_id {y} = ?ltr_rtl_trans_id_0
  rtl_ltr_id = ?rtl_ltr_trans_id_1
