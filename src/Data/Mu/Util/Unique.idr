module Data.Mu.Util.Unique 
import Data.Mu.Util.Relude
public export
0 Unique' : Type -> Type  
Unique' t = {x, y : t} -> x === y
public export
record Unique (t : Type) where 
  constructor MkUnique 
  0 witness : t
  0 uniq : Unique' t

-- %defaulthint
public export
etaEq : {0 a, b : Type} -> {0 f, g : a -> b} -> (0 prf : ((x : a) -> f x === g x)) => f === g
etaEq = believe_me ()
-- %defaulthint
public export
etaEqL : {0 a, b : Type} -> {0 f, g : (1 _ : a) -> b} -> (0 prf : ((x : a) -> f x === g x)) => f === g
etaEqL = believe_me ()
-- %defaulthint
 
public export
0 uniqueEq : {t : Type} -> (u : Unique t) -> (x, y : t) -> x === y
uniqueEq {t} (MkUnique w u) {x,y} = u {x,y}
public export
0 witness' : (t : Type) -> Unique t -> t
witness' t (MkUnique w u) = w
public export
0 uniq' : (t : Type) -> Unique t -> Unique' t
uniq' t (MkUnique w u) = u
private
uniqueUnit' : Unique' ()
uniqueUnit' {x=(), y=()} = Refl
public export
uniqueUnit : Unique ()
uniqueUnit = MkUnique () uniqueUnit' 
private
uniquePair' : Unique' a -> Unique' b -> Unique' (a, b)
uniquePair' ua ub {x=(x1, y1)} {y=(x2, y2)} = 
  let prfX : x1 === x2

      prfY : y1 === y2
  in rewrite prfX in rewrite prfY in Refl
-- %defaulthint
public export
uniquePair : Unique a -> Unique b -> Unique (a, b)
uniquePair (MkUnique wa ua) (MkUnique wb ub) = MkUnique (wa, wb) (uniquePair' ua ub)

private
0 uniqueFun' : Unique' b -> Unique' (a -> b)
uniqueFun' ub {x=f, y=g} = 
  let prf : (x' : a) -> f x' === g x'
      prf x' = ub {x=f x'} {y=g x'}
  in etaEq @{prf}

-- %defaulthint
public export
0 uniqueFun : Unique b => Unique (a -> b)
uniqueFun @{MkUnique w ub} = MkUnique (\_ => w) (uniqueFun' ub)

-- %defaulthint
 
public export
0 use_unique : Unique t => Unique' t
use_unique @{MkUnique w u} = u

-- %defaulthint
 
public export
unique : (0 _ : a) => (0 _ : Unique' a) => Unique a
unique @{w} @{u} = MkUnique w u
-- %defaulthint
 
public export
0 uniqueFunUniqueResult : Unique (a -@ b) => {0 f, g : a -@ b} -> f x === g x
uniqueFunUniqueResult @{MkUnique w u} {f} {g} = rewrite (u {x=f,y=g}) in Refl
