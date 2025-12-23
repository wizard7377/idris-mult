module Data.Grade.List.Lemma
import Data.Grade.List.Types
import Data.Grade.List.Ops
import Relude

export
decAny : Drop a => {1 xs : QList a} -> (ans : (1 x : a) -> Dec (p x)) -> Dec (Any p xs)
decAny {xs=Nil} ans = ?dec_any
decAny {xs=(x :: xs')} ans = case ans x of 
  Yes prf => (drop xs') `seq` (Yes (Here prf))
  No contra => case decAny {xs=xs'} ans of
    Yes prf' => Yes (There prf')
    No contra' => No (\case 
      Here prf => contra prf
      There prf' => contra' prf')

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
SingleEquiv : Any p [x] <=> p x
SingleEquiv = MkEquivalence to from 
  where
    to : Any p [x] -> p x
    to (Here prf) = prf
    to (There prf) impossible 
    from : p x -> Any p [x]
    from prf = Here prf

export 
NoneEquiv : (Any p []) -> Void
NoneEquiv (Here prf) impossible 
NoneEquiv (There prf) impossible
