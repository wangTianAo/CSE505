sublist(L1,L2):-
	append(A,B,L2),
	append(L1,C,B).

append([],A,A).
append([X|A],B,[X|C]):-
	append(A,B,C).