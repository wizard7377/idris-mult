# First Order Multiplicities 

Idris' use of Quantatitive Type Theory is one of its more distincitive features.
However, it lacks in multiplicity polymorphism, that is, the ability to reflect on multiplicities 

## Paper 

The paper may be found at 
## Preliminaries 

First, we define a number of neccassary properties 

### Copying and Droping 

In Rust, the two most important traits are `Copy` (or its explicit form, `Clone`), and `Drop`.
While Idris 2 does have a number of similarities to Rust with respect to linear typing, it is unfourtanetly impossible to actually create `Clone`.
This is because we would have to have a way to derive the following: `ctx |- Copy<a>, (1 x : a) ==> ctx |- (1 x : a), (1 x.copy : a)`, which requires similtaneously using and not using the value.
However, we can derive an incredibly similar form, which we also call `Copy`. 

#### [Copy](./idris-copy/src/Prelude/Copy.idr)

Copy has the following type: 

```
interface Copy a where
  constructor MkCopy
  1 copy : 
    {0 b : a -> a -> Type} ->
    (1 x : a) -> 
    (1 f : (1 y : a) -> (1 z : a) -> b y z) -> 
    b x x
```

We also have a version of `copy` for some independent `b`, which we call `copy'`:

```
copy' : (1 _ : Copy a) => a -@ (a -@ a -@ b) -@ b 
copy' @{(MkCopy copy_inst)} x f = copy_inst x f
```

This type is a fiar bit more telling then the other, as we have a way to "use" the input twice. 
Note that these types are sufficent for deriving a proof that these are reflectably equal.

For instance, given `1 g : (1 y : a) -> (1 z : a) -> (0 _ : y = x) -> (0 _ : z = x) -> c y z`, we can first apply `copy x g`, yielding `x = x -> x = x -> c x x`, which can be trivially converted to `c x x`.
This operations is so important it gets its own name, `copyWithEq`[^1]

```
copyWithEq : 
    forall a.
    {0 b : a -> a -> Type} ->
    (1 _ : Copy a) => 
    (1 x : a) ->
    ((1 y : a) -> (1 z : a) -> (0 prfY : y === x) => (0 prfZ : z === x) => b y z) -@
    b x x
```
<!-- TODO Add examples -->

#### [Drop](./idris-copy/src/Prelude/Copy.idr) 

`Drop` generalizes the notion of "deleting a value"

<!--- TODO --->

#### [Clone](./idris-copy/src/Prelude/Clone.idr)
<!--- TODO --->
### [Linear Natural Numbers](./idris-mult/src/Data/Grade/QNat.idr) 
<!--- TODO --->
### Linear Lists and Vectors 
<!--- TODO --->
### Linear Pair Types 
<!--- TODO --->
## Mu Types 
<!--- TODO --->
## Formula Language 
<!--- TODO --->
## [Omega Types](./idris-mult/src/Data/Grade/Omega.idr) 
<!--- TODO --->
## Usage 
<!--- TODO ---> 


[^1]: There's also a `copyWithEq'` for an independent version
