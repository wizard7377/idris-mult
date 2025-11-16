module Data.Grade.Util.Relude

import public Builtin
import public Prelude.Basics
import public Prelude.Cast
import public Data.Grade.Util.Types
import public Data.Grade.QNat
import public Data.Nat
import public Data.Linear.Notation
import public Data.Linear.Interface
import public Data.Linear.LEither
import public Prelude.Num
import public Prelude.Ops
import public Prelude.Types
import public Prelude.Uninhabited
import public Data.Grade.Util.Ops

%inline %tcinline
public export %unsafe
trust_me : a -@ b
trust_me x = prim__believe_me a b x
%inline %tcinline
public export %unsafe
axiom : a
axiom = prim__believe_me () a ()
