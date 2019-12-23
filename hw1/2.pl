delete(X,[X|Ys],Ys).
delete(X,[Y|Ys],[Y|Zs]):-
	delete(X,Ys,Zs) .