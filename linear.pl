% Taken from Standford Encyclopedia of Philosophy entry on Linear Logic

prove(R,[A],[B]) :- A = B, !, R = init(A), !.
prove(R,A,B) :-
    prove(R1,A1,[B1|C]),
    prove(R2,[A2|C],B2),
    append(A1,A2,A),
    append(B1,B2,B)
    ->
    R = cut(R1,R2,C).
prove(R,[neg(P)|A],B) :-
    prove(R1,A,[P|B])
    ->
		R = lneg(R1).

prove(R,A,[neg(P)|B]) :-
    prove(R1,[P|A],B)
    ->
    R = rneg(R1).
prove(R,[one|A],B) :-
		prove(R1,A,B) ->
		R = lone(R1).
prove(R,[],[one]) :-
		once(R = rone).
prove(R,[bot],B) :-
		once(R = lbot(B)).
prove(Prf,A,[bot|B]) :-
    prove(Prf1,A,B),
    Prf = rbot(Prf1),
    !.
prove(Prf,[times(B1,B2)|X],Y) :-
    prove(Prf1,[B1,B2|X],Y),
    Prf = ltimes(Prf1,B1,B2),
    !.
prove(Prf,X,[times(B1,B2)|Y]) :-
    prove(Prf1,X1,[B1|Y1]),
    prove(Prf2,X2,[B2|Y2]),
    append(X1,X2,X),
    append(Y1,Y2,Y),
    Prf = rtimes(Prf1,Prf2),
    !.
