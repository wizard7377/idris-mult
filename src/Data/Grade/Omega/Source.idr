module Data.Grade.Omega.Source 

import Data.Grade.Omega.Types
import Data.Grade.Form
import Data.Grade.Util.Relude
import Data.Grade.Logic
public export
data Stream : (t : Type) -> (x : t) -> Type where
  (::) : (1 x : t) -> (1 xs : Stream t x) -> Stream t x

public export
0 Source : (t : Type) -> (w : t) -> Type
Source t w = Stream (Omega' FVar t w) ?source_example

export 
splitStream : Stream t x -@ Duple (Stream t x) (Stream t x)
splitStream (x :: r) = let For xs ys = splitStream r in (For (x :: xs) ys)
