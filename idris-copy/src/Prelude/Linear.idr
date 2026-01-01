module Prelude.Linear
import Prelude.Copy
import Data.Linear.Notation

-- public export
-- infixr 0 ⊸

public export
⊸ : Type -> Type -> Type
⊸ = (-@)
public export
data Lin : Type -> Type where
  Once : (1 _ : a) -> Lin a
public export
data Irr : Type -> Type where
  Erase : (0 _ : a) -> Irr a
public export
data Bang : Type -> Type where
  Sure : (_ : a) -> Bang a

public export
Copy (Bang a) where
  copy (Sure x) f = f (Sure x) (Sure x)
public export
Drop (Bang a) where
  drop (Sure a) = ()
public export
Copy (Irr a) where
  copy (Erase a) f = f (Erase a) (Erase a)
public export
Drop (Irr a) where
  drop (Erase a) = ()
