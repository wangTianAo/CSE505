propositions(P,L):-
	propositions_Helper(P,L,[]).

propositions_Helper([],L,LTemp):-
	sort(LTemp,L).
propositions_Helper([rule(A,B)|T],L,LTemp):-
	append(B,[A],L1),
	append(L1,LTemp,L2),
	propositions_Helper(T,L,L2).

tp(P, M1, M2):-
	tp_Helper(P,M1,M1,M2).

tp_Helper([],M1,MTemp,M2):-
	sort(MTemp,M2).
tp_Helper([rule(A,B)|T],M1,MTemp,M2):-
	(
		subset(B,M1)->
		append(MTemp,[A],M3),
		tp_Helper(T,M1,M3,M2);
		tp_Helper(T,M1,MTemp,M2)
	).

leastmodel(P,M):-
	leastmodel_Helper(P,M,[]).

leastmodel_Helper(P,M,M1):-
	tp(P,M1,M2),
	(
		M1\=M2->
		leastmodel_Helper(P,M,M2);
		M = M2
	).

append([],A,A).
append([X|A],B,[X|C]):-
	append(A,B,C).

subset([],[]).
subset([X|L],[X|S]) :-
    subset(L,S).
subset(L, [_|S]) :-
    subset(L,S).