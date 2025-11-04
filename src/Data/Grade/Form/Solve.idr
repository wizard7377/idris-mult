module Data.Grade.Form.Solve 

import Data.Grade.Form.Types 
import Data.Grade.Form.Ops 
import Data.Grade.Form.Lemma 
import Data.Grade.Util.Relude
import Data.Grade.Util.LPair
%default total
export 
0 Ans : Form -> QNat -> QNat -> Type 
Ans f x y = (Eval f x) === y

mutual 
  private 
  0 solveVar' : (y : QNat) -> Dec (Subset QNat (\x => Ans (FVar) x y))
  solveVar' y = Yes (Element y Refl)

  private 
  0 solveVal' : (n : QNat) -> (y : QNat) -> Dec (Subset QNat (\x => Ans (FVal n) x y))
  solveVal' Zero Zero = Yes (Element Zero Refl) 
  solveVal' (Succ n) (Succ y) = case solveVal' n y of 
    Yes (Element x prf) => Yes (Element (Succ x) (rewrite prf in Refl))
  solveVal' Zero (Succ y) = No (\(Element x prf) => neq_succ' prf)
  solveVal' (Succ n) Zero = No (\(Element x prf) => neq_succ prf)
  private 
  0 solveApp' : (f1 : Form) -> (f2 : Form) -> (y : QNat) -> Dec (Subset QNat (\x => Ans (FApp f1 f2) x y))
  solveApp' f1 f2 y = let 
    solve_f1 : Dec (Subset QNat (\z => Ans f1 z y))
    solve_f1 = solve' f1 y
    in case solve_f1 of 
      Yes (Element z prf1) => let 
        solve_f2 : Dec (Subset QNat (\x => Ans f2 x z))
        solve_f2 = solve' f2 z
        in case solve_f2 of 
          Yes (Element x prf2) => ?h4
          No contra2 => ?h3
      No contra1 => ?h2
  private 
  solveAdd' : (f1 : Form) -> (f2 : Form) -> (y : QNat) -> Dec (Subset QNat (\x => Ans (FAdd f1 f2) x y))
  private 
  solveMul' : (f1 : Form) -> (f2 : Form) -> (y : QNat) -> Dec (Subset QNat (\x => Ans (FMul f1 f2) x y))
  private 
  solveMax' : (f1 : Form) -> (f2 : Form) -> (y : QNat) -> Dec (Subset QNat (\x => Ans (FMax f1 f2) x y))
  solveMin' : (f1 : Form) -> (f2 : Form) -> (y : QNat) -> Dec (Subset QNat (\x => Ans (FMin f1 f2) x y))
  ||| NOTE: This is not actually solveable, however, we consider only cases where FFun does not appear
  solveLeft' : (f : Form) -> (y : QNat) -> Dec (Subset QNat (\x => Ans (FLeft f) x y))
  solveRight' : (f : Form) -> (y : QNat) -> Dec (Subset QNat (\x => Ans (FRight f) x y))
  private 
  0 solve' : (f : Form) -> (y : QNat) -> Dec (Subset QNat (\x => Ans f x y))
  solve' f y = case f of 
    FVar => solveVar' y
    FVal n => solveVal' n y
    FApp f1 f2 => solveApp' f1 f2 y
    FAdd f1 f2 => solveAdd' f1 f2 y
    FMul f1 f2 => solveMul' f1 f2 y
    FMin f1 f2 => solveMin' f1 f2 y
    FMax f1 f2 => solveMax' f1 f2 y
    FLeft f0 => solveLeft' f0 y
    FRight f0 => solveRight' f0 y

public export
0 solve : (f : Form) -> (y : QNat) -> Dec (Solve f y)
solve f y = case solve' f y of 
    Yes (Element x prf) => Yes (Element x prf)
    No contra => No (\(Element x prf) => contra (Element x prf))

