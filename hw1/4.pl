delete_sublist(L1,L2,L3):-
	append(B,A,L2),
	append(L1,C,A),
	append(B,C,L3).

append([],A,A).
append([X|A],B,[X|C]):-
	append(A,B,C).