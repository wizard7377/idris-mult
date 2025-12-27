module Data.Grade.List.Lemma
  
import Data.Grade.List
import Relude
import Data.Grade.Sigma 
import Decidable.Equality
import Data.Grade.Logic as Logic
export
decAny : Drop a => {1 xs : QList a} -> (ans : (1 x : a) -> Dec (p x)) -> Dec (Any p xs)
decAny {xs=Nil} ans = ?dec_any
decAny {xs=(x :: xs')} ans = case ans x of 
  Yes prf => (drop xs') `seq` (Yes (Because prf))
  No contra => case decAny {xs=xs'} ans of
    Yes prf' => Yes (However prf')
    No contra' => No (\case 
      Because prf => contra prf
      However prf' => contra' prf')

export 
decAll : Drop a => {1 xs : QList a} -> (ans : (1 x : a) -> Dec (p x)) -> Dec (All p xs)
decAll {xs=Nil} ans = Yes Done
decAll {xs=(x :: xs')} ans = case ans x of
    Yes prf => case decAll {xs=xs'} ans of
        Yes prf' => Yes (Also prf prf')
        No contra' => No (\case 
            Done impossible
            Also prf'' prf''' => contra' prf''')
    No contra => drop xs' `seq` No (\case
        Done impossible
        Also prf'' prf''' => contra prf'')

export 
decElem : Drop a => DecEq a => {0 x : a} -> {1 xs : QList a} -> Dec (IsElem x xs)
decElem {xs} = let 
  res = decAny {xs} (\y => drop y `seq` Logic.decScandel (decEq x y))
  in case res of
    Yes prf => Yes (AnyElem prf)
    No contra => No (\prf => contra (ElemAny prf))

export 
SingleEquiv : Any p [x] <=> p x
SingleEquiv = MkEquivalence to from 
  where
    to : Any p [x] -> p x
    to (Because prf) = prf
    to (However prf) impossible 
    from : p x -> Any p [x]
    from prf = Because prf

export 
NoneEquiv : (Any p []) -> Void
NoneEquiv (Because prf) impossible 
NoneEquiv (However prf) impossible
export
App2ElemExists : {0 f : QNat -@ QNat -@ QNat} -> {1 z : QNat} -> {auto 0 prf : IsElem z (App2 f xs ys)} -> (Sigma QNat $ \x => Subset QNat $ \y => Tuple [IsElem x xs, IsElem y ys, (f x y === z)])
App2ElemExists {z} @{prf} = prim__believe_me ? ? z
