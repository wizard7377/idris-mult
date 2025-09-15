# First Order Multiplicities 

Idris' use of Quantatitive Type Theory is one of its more distincitive features.
However, it lacks in multiplicity polymorphism, that is, the ability to reflect on multiplicities 

## The type μ

μ (in Idris `M`, both standing for "multiplicity") serves to model multiplicities. 
At its core, it's simply a `LVect` or `Copies`, with the cavaet that it can be assumed that all its elements are the same. 
Its definition is:

```idris2
data M : (0 n : Nat) -> (t : Type) -> Type where
    MS : (1 x : t) -> (1 xs : (Lazy (M n t))) -> M (S n) t
    MZ : M Z t
```


We can use this to model multiplicities[^1]. `1` is simply `M 1`. There is only one way to construct such a value, `MS x MZ`, where `x` is `1 x : t`.

### $1 + 1 = 2$

In general, many intutions about `LVect` `Copies`, and most important, `Nat` itself, apply to `μ`. 
Firstly, there is a function $\boxplus$ such that if $a + b = c$ then $μ_a T \boxplus μ_b T \equiv μ_c T$.
It is called combine, and is written as 

```idris2
combine : {t : Type} -> {0 a, b : Nat} -> M a t -@ M b t -@ M (a + b) t
combine MZ y = y
combine (MS x xs) y = MS x (combine xs y)
```

We also have the equivalent of mutiplication, $\boxtimes$, which is called flatten:

```idris2
flatten : {t : Type} -> {0 a, b : Nat} -> (M a (M b t) -@ M (a * b) t)
flatten (MS x xs) = combine x (flatten xs)
flatten MZ = MZ
```

## The type ω

## Linear Interfaces

[^1]: Non-zero ones, anyway
