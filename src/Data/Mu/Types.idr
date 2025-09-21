module Data.Mu.Types 
import Prelude
  
||| The Mu type, very similar to `copies`
||| See this https://discord.com/channels/827106007712661524/861620883893911582/1419135657862893639 and https://discord.com/channels/827106007712661524/861620883893911582/1419139468031688795 for the final design
||| 
||| @ t type of the copies
||| @ n number of copies
||| @ x the value to be copied
public export
data M : {0 t : Type} -> (n : Nat) -> (x : t) -> Type where
    MS : (1 x : t) -> (1 xs : Lazy (M n x)) -> M (S n) x
    MZ : {0 x : t} -> M Z x

export 
infixl 1 ^
public export 
record (^) (0 t : Type) (n : Nat) where
    constructor Many
    0 witness : t
    1 supply : M {t=t} n witness
    
