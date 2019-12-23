flatten([],[]).
flatten(X,[X]):- \+ is_list(X).
flatten([X|Tail],Z):-
	flatten(X,Y),
	flatten(Tail,Ys),
	append(Y,Ys,Z).

append([],A,A).
append([X|A],B,[X|C]):-
	append(A,B,C).