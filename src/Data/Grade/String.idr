module Data.Grade.String
import public Builtin
import Data.Linear.Notation
import Data.Linear.Interface
import Data.Linear.Copies

public export
data LString : Type where 
  MkLString : (1 str : String) -> LString
  
export  
unLString : LString -@ String
unLString (MkLString str) = str
export
mkLString : String -@ LString
mkLString str = MkLString str

public export
Consumable LString where
  consume (MkLString str) = assert_linear (\_ => ()) str


public export
interface LShow t where
  lshow : t -@ LString

public export
LShow LString where 
  lshow str = str
