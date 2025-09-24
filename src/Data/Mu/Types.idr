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
    ||| Give one more copy
    ||| @ n Number of copies given (result - 1)
    ||| @ x The value being copied
    ||| @ xs The remaining copies
    Provide : 
      {0 t : Type} -> 
      {0 n : Nat} -> 
      (1 x : t) -> 
      (1 xs : Lazy (Source {t=t} n x)) -> 
      Source {t=t} (S n) x
    ||| No more copies available
    Exhaust : 
      {0 t : Type} -> 
      {0 x : t} -> 
      Source Z x
public export
data M' : (0 n : Nat) -> (0 t : Type) -> (0 x : t) -> Type where
    ||| Give one more copy
    ||| @ n Number of copies given (result - 1)
    ||| @ x The value being copied
    ||| @ xs The remaining copies
    MZ : 
      M' Z t x
    ||| No more copies available
    MS : 
        (1 x : t) -> 
        (1 xs : Lazy (M' n t x)) -> 
        M' (S n) t x
 
||| The Mu type, very similar to `copies`
public export 
data M : (0 n : Nat) -> (0 t : Type) -> Type where
    ||| A witness that all copies are the same, combined with a source
    Supply : (0 witness : t) -> (1 source : Source {t=t} n witness) -> M n t
    
public export 
0 (.witness) : {0 n : Nat} -> {0 t : Type} -> (1 x : M n t) -> t
(.witness) {n=n} {t=t} (Supply w s) = w
public export
(.source) : {0 n : Nat} -> {0 t : Type} -> (1 x : M n t) -> Source {t=t} n (x .witness)
(.source) {n=n} {t=t} (Supply w s) = s
%inline %tcinline
public export
Proj : Type 
Proj = Nat -@ Nat
||| The Ω type, which can produce any number of `t` that are projected to by `p`
||| Useful, as this allows there to be functor from the type of ℒ of `M` to ℒ of `Ω`
public export 
W : (0 p : Proj) -> (0 t : Type) -> Type
W p t = (1 n : Nat) -> M (p n) t

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
(^-) : (0 t : Type) -> (0 p : Proj) -> Type
(^-) t p = W p t
  
  
||| The fact that two `M` values contain the same elements
public export
0 Like : {0 t : Type} -> {0 n, m : Nat} -> (M n t) -> (M m t) -> Type
Like {t=t} {n=n} {m=m} (Supply w0 _) (Supply w1 _) = (w0 === w1)


%inline %tcinline
public export
0 MapTo : (p : Proj) -> (n : Nat) -> Type
MapTo p n = (m : Nat ** ((p m) === n))

public export
exhaust : {0 t : Type} -> {auto 0 x : t} -> M 0 t
exhaust @{x} = Supply x Exhaust
public export
provide : {0 t : Type} -> {0 n : Nat} -> (1 x : t) -> (1 ys : M n t) -> {auto 0 prf : ys.witness === x} -> M (S n) t
provide x (Supply witness source) @{prf} = Supply x (Provide x (Delay (rewrite sym prf in source)))

public export
question : {0 t : Type} -> {0 x : t} -> (1 _ : Source (S n) x) -> M (S n) t
question (Provide x xs) = Supply x (Provide x xs)
