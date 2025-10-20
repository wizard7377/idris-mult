module Tests.Omega

import Prelude
import Data.Mu
import Data.Mu.LNat
import Data.Linear.Notation
import Data.Linear.Interface
import Data.Mu.Set
public export
0 MostOnce : ? -> ? -> ?
MostOnce t w = Omega (SElem [0, 1]) t w

public export
1 ex_1_1 : MostOnce ((1 k : LNat) -> LNat) (ladd (mkLN 7))
ex_1_1 = gen' (MkBang fun)
  where 
    fun : LNat -@ LNat
    fun = ladd (mkLN 7)
1 ex_1_2 : MostOnce ((1 k : LNat) -> LNat) (ladd (mkLN 7))
ex_1_2 {n=Zero} = MZ
ex_1_2 {n=(Succ Zero)} = MS (ladd (mkLN 7)) MZ 
ex_1_2 {n=(Succ (Succ n))} @{prf} = let 
  prf0 : Either (Succ Zero = Succ (Succ n)) Void
  prf0 = ?p0
  prf1 : Void
  prf1 = ?p1
  in seq n (absurd prf1)

1 ex_2_1 : MostOnce LNat (ladd (mkLN 7) (mkLN 3)) 
ex_2_1 = ?ef
public export
omegaTest : IO ()
omegaTest = pure ()
