module Data.Grade.Omega.Lemma 
import Data.Grade.Omega.Types
import Data.Grade.Mu
import Data.Grade.List
import Relude
%default total
public export
SingleOmegaToMu : 
  {n : QNat} ->
  Omega [n] t w -@ Mu n t w
SingleOmegaToMu omega = omega n

public export
MuToSingleOmega : 
  {n : QNat} ->
  Mu n t w -@ Omega [n] t w
MuToSingleOmega = ?mu_to_single_omega_rhs 
