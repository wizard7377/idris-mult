module Data.Mu.Types 
import Data.Mu.Util.Relude
  
||| The Mu type, very similar to `copies`
||| See this https://discord.com/channels/827106007712661524/861620883893911582/1419135657862893639 and https://discord.com/channels/827106007712661524/861620883893911582/1419139468031688795 for the final design
||| 
||| @ t type of the copies
||| @ n number of copies
||| @ x the value to be copied
public export
data Source : {0 t : Type} -> (0 n : Nat) -> (0 x : t) -> Type where
    Provide : {0 t : Type} -> {0 n : Nat} -> (1 x : t) -> (1 xs : Lazy (Source {t=t} n x)) -> Source {t=t} (S n) x
    Exhaust : {0 t : Type} -> {0 x : t} -> Source Z x
 
public export 
data M : (0 n : Nat) -> (0 t : Type) -> Type where
    Supply : (0 witness : t) -> (1 source : Source {t=t} n witness) -> M n t
    

||| The Ω type, which can produce any number of `t` that are projected to by `p`
||| Useful, as this allows there to be functor from the type of ℒ of `M` to ℒ of `Ω`
public export 
W : (0 p : Nat -> Nat) -> (0 t : Type) -> Type
W p t = (0 n : Nat) -> M (p n) t

||| The ω type, which can produce any number of `t`
%inline %tcinline
public export 
Omega : (0 t : Type) -> Type
Omega t = W id t

export 
infixl 1 ^
public export
(^) : (0 t : Type) -> (0 n : Nat) -> Type
(^) t n = M n t

export 
infixl 1 ^-
public export
(^-) : (0 t : Type) -> (0 p : Nat -> Nat) -> Type
(^-) t p = W p t
  
  
||| The fact that two `M` values contain the same elements
public export
0 Like : {0 t : Type} -> {0 n, m : Nat} -> (M n t) -> (M m t) -> Type
Like {t=t} {n=n} {m=m} (Supply w0 _) (Supply w1 _) = (w0 === w1)

