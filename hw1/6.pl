change([],0,[]).
change([H|Xs],Value,[C|Cs]):-
	A is floor(Value/H),
	change_helper(0,A,C),
	ValueRest is Value-(C*H),
	change(Xs,ValueRest,Cs).

change_helper(X,Number,C):-
	X<Number,
	XNew is X+1,
	change_helper(XNew,Number,C).

change_helper(X,Number,C):-
	X=<Number,
	C is X.