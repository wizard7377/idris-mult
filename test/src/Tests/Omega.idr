module Tests.Omega

import Prelude
import Data.Mu
import Data.Grade.QNat
import Data.Linear.Notation
import Data.Linear.Interface
import Data.Grade.Set

public export
0 MostOnce : ? -> ? -> ?
MostOnce t w = Omega (FRange 0 1) t w

public export
omegaTest : IO ()
omegaTest = pure ()
