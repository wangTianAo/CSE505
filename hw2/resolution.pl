resolution():-
	findall([N,X],myClause(N,X),OriClause),
	findall([N,X],myQuery(N,X),QueryClause),
	%writeln(OriClause),
	%writeln(QueryClause),

	getNeg(QueryClause,NegQueryClause),
	%writeln(NegQueryClause),
	%writeln(NegQueryClause),
	append(OriClause,NegQueryClause,AllClause),
	%writeln(AllClause),

	decomOr(AllClause, L),
	length(L,0,Num),
	NumNext is Num+1,
	%writeln(L),
	%writeln(NumNext),

	res(L,[],NumNext).
	
res(L,ResL,Num):-
	(
		%writeln('now L'+ L),
		member(X,L),
		member(Y,L),
		X\=Y,
		X = [Num1,Clause1],
		Y = [Num2,Clause2],

		%find complementary
		haveComplementary(Clause1,Clause2,Com),
		delete(Com,Clause1,Clause3),
		delete(neg(Com),Clause3,Clause4),
		delete(Com,Clause2,Clause5),
		delete(neg(Com),Clause5,Clause6),
		(
			(Clause4=[],Clause6=[])->
			% if both clauses are empty, resolution success
			writeln('resolution(success)'),
			append(ResL,[[Num1,Num2,'empty',Num]],NewResL),
			printResults(NewResL);

			% if not, create new clause and check whether it is legal and do recursion
			append(Clause4,Clause6,NewClauseWithDup),
			removeDup(NewClauseWithDup,NewClause),
			\+ isTautology(NewClause),
			\+ duplicateRule(NewClause,L),
			append(ResL,[[Num1,Num2,NewClause,Num]],NewResL),
			append(L, [[Num, NewClause]], NewL),
			%writeln('NewL is '+ NewL),
			NumNext is Num+1,
			res(NewL,NewResL,NumNext)
		)
	);
	writeln('resolution(fail)').

getNeg([[N,or(X,Y)]],New):-
	getNeg([[N,X]],New1),
	NumNext is N+1,
	getNeg([[NumNext,Y]],New2),
	append(New1,New2,New).
getNeg([[N,X]],[[N,neg(X)]]):-
	X \= or(_,_).
getNeg([[N,neg(X)]],[[N,X]]).

formOr(empty, empty).
formOr([X], X).
formOr([H1,H2|T], or(H1,L)):-
	formOr([H2|T], L).

show([Num1,Num2,Clause,Num3]):-
	formOr(Clause, ClauseAfterBuildOr),
	writeln(resolution(Num1, Num2, ClauseAfterBuildOr, Num3)).

printResults([]).
printResults([H|T]):-
	show(H),
	printResults(T).

subset([], _).
subset([H|T], L) :-
	member(H,L),
	subset(T,L).

duplicateRule(C, L) :-
	member([_, X], L),
	subset(C, X),
	subset(X, C).

getSingleNeg(neg(H),H).
getSingleNeg(H,neg(H)).

isTautology([H]):- fail.
isTautology([H|T]):-
	getSingleNeg(H,AfterH),
	member(AfterH,T)->
	true;
	isTautology(T).

removeDup([],[]).
removeDup([H|T],[H|NewList]):-
	\+ member(H,T),
	removeDup(T,NewList).
removeDup([H|T],NewList):-
	member(H,T),
	removeDup(T,NewList).

haveComplementary(Clause1,Clause2,Com):-
	member(C1,Clause1),
	member(C2,Clause2),
	((neg(C1)=C2,Com = C1);
	(neg(C2)=C1,Com = C2)).

length([], Length, Length).
length([_|L], N, Length) :-
        N1 is N+1,
        length(L, N1, Length).

delete(X,[],[]).
delete(X, [X|Ys], Ys).
delete(X, [Y|Ys], [Y|Zs]) :-
	X \= Y,
	delete(X, Ys, Zs).

member(X, [X|_]).
member(X, [_|Ys]) :-
	member(X,Ys).

decomOr([],[]).
decomOr([[N,X]|T1],[[N,L]|T2]):-
	removeOr(X,L),
	decomOr(T1,T2).

removeOr(or(X, Y), L) :-
	removeOr(X, L1),
	removeOr(Y, L2),
	append(L1, L2, L).

removeOr(X, [X]).

append([],A,A).
append([X|A],B,[X|C]):-
	append(A,B,C).