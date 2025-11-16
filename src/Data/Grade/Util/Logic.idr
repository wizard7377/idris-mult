module Data.Grade.Util.Logic

import public Data.Grade.Util.LPair
import Builtin
import Prelude.Types
import Prelude.Basics
public export
0 DecFlatten : Dec (Dec a) -> Dec a
DecFlatten (Yes (Yes x)) = Yes x
DecFlatten (Yes (No contra)) = No contra
DecFlatten (No contra) = No (\x => contra (Yes x))
