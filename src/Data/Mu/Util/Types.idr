module Data.Mu.Util.Types
 
%inline %tcinline
public export
LConst : (1 _ : b) -> ((_  : a) -> b)
LConst {a} x y = x
%inline %tcinline
public export
Const : (_ : b) -> ((_ : a) -> b)
Const {a} x y = x
 
%inline %tcinline
public export
LCompose : (f : (1 _ : a) -> b) -> (g : (1 _ : b) -> c) -> ((1 _ : a) -> c)
LCompose f g x = g (f x)

%inline %tcinline
public export
Compose : (f : a -> b) -> (g : b -> c) -> (a -> c)
Compose f g x = g (f x)
