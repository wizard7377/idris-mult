module Data.Mu.Util.Nat  
import Data.Mu.Util.Relude
import Data.Linear.LNat
import Prelude.Uninhabited

public export
data Qty : Type where 
    Z : Qty
    S : (1 k : Qty) -> Qty

public export
toQty : LNat -@ Qty
toQty Zero = Z
toQty (Succ k) = S (toQty k)
public export
fromQty : Qty -@ LNat
fromQty Z = Zero
fromQty (S k) = Succ (fromQty k)
%inline %tcinline 
public export
safeMinus : (a : Nat) -> (b : Nat) -> {auto 0 prf : (LTE b a)} -> Nat
safeMinus a b = minus a b

%hint
export
0 lteSquash : {x : Nat} -> {auto 0 prf : LTE x 0} -> (x === 0)
lteSquash {x=Z} = Refl

%hint 
export 
0 lteRefl : {x : Nat} -> LTE x x
lteRefl {x=Z} = LTEZero
lteRefl {x=(S k)} = LTESucc lteRefl
%hint 
private
0 multSuccAddLemma2 : {a : Nat} -> (a * 1) === (a + 0)
multSuccAddLemma2 {a=Z} = Refl
multSuccAddLemma2 {a=(S a')} = rewrite multSuccAddLemma2 {a=a'} in %search
%hint
private 
0 multSuccAddLemma1 : {a, b : Nat} -> (a * 1) === (a + (a * 0))
multSuccAddLemma1 {a=Z} {b=b} = Refl
multSuccAddLemma1 {a=a} {b=Z} = rewrite multZeroRightZero a in multSuccAddLemma2 {a=a}
multSuccAddLemma1 {a=(S a')} {b=(S b')} = rewrite multSuccAddLemma1 {a=a'} {b=(S b')} in %search

%hint 
private 
0 plusSwap2 : {a, b, c : Nat} -> (a + (b + c)) === (b + (a + c))
plusSwap2 = ?hplusSwap2
%hint 
export 
0 multSuccAdd : {a, b : Nat} -> (a * (S b)) === (a + (a * b))
multSuccAdd {a=Z} {b=b} = %search
multSuccAdd {a=a} {b=Z} = multSuccAddLemma1 {a=a} {b=Z}
multSuccAdd {a=(S a')} {b=b} = let 
  goal1 : (b + (a' * (S b))) === (b + (a' + (a' * b)))
  goal0 : (b + (a' * (S b))) === (a' + (b + (a' * b)))
  goal0 = ?h0
  goal : S (b + (a' * (S b))) === S (a' + (b + (a' * b)))
  goal = cong S goal0 in goal

%hint 
export 
0 plusZeroBoth : {a, b : Nat} -> {auto 0 prf : (a + b) === Z} -> (a === Z, b === Z)
plusZeroBoth {a=Z} {b=Z} @{prf} = (Refl, Refl)
plusZeroBoth {a=Z} {b=(S b')} @{prf} = absurd $ sym prf
plusZeroBoth {a=(S a')} {b=b} @{prf} = absurd $ sym prf
