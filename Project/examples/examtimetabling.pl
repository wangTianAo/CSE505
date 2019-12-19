:- use_module('./bee/beeCompiler/bCompiler.pl', [bCompile/2]).
:- use_module('./bee/satsolver/satsolver.pl', [sat/1]).
:- use_module('./bee/beeCompiler/bDecode.pl', [decodeIntArray/2]).
:- use_module('./cliquer/plcliquer.pl').

exam(0,8,2).
exam(1,10,3).
exam(2,7,4).
exam(3,12,2).
exam(4,5,1).
exam(5,1,7).
classroomNum(3).

examtimetabling():-
	findall(exam(ExamName,StartTime,LastTime),exam(ExamName,StartTime,LastTime),Timetable),
	findall(Num,classroomNum(Num),K),
	item_at(1,K,KColors),
	writeln(Timetable),
	writeln("KColors"+KColors),
	length(Timetable,Length),
	writeln(Length),
	generateEmptyGraph(Length,Graph),
	writeln(Graph),

	combineAlllist(Timetable,AllCombWithDup),
	removeDup(AllCombWithDup,AllComb),
	writeln(AllComb),

	combinenotDisturblist(Timetable,AllNotDisturbCombWithDup),
	removeDup(AllNotDisturbCombWithDup,AllNotDisturbComb),
	writeln(AllNotDisturbComb),

	remove_list(AllComb,AllNotDisturbComb,DisturbExam),
	writeln(DisturbExam),
	writeln(Graph),

	changeGraph(DisturbExam,Graph,NewGraph),
	writeln(NewGraph),

	schedule_time(NewGraph, KColors, Coloring),
	writeln(KColors),
	writeln(Coloring).

item_at( N, L, Item ) :-
    item_at( N, 0, L, Item ).   
item_at( N, Count, [H|_], Item ) :-
    CountNew is Count + 1,
    CountNew = N,
    Item = H.
item_at( N, Count, [_|T], Item ) :-
    CountNew is Count + 1,
    item_at( N, CountNew, T, Item ).
    
changeGraph([],NewGraph,NewGraph).
changeGraph([[exam(ExamName1,StartTime1,LastTime1),exam(ExamName2,StartTime2,LastTime2)]|T],
	Graph,NewResult):-
	%writeln(ExamName1),
	%writeln(ExamName2),
	replace(Graph,ExamName1,ExamName2,1,NewGraph1),
	replace(NewGraph1,ExamName2,ExamName1,1,NewGraph),
	changeGraph(T,NewGraph,NewResult).


replace( L , X , Y , Z , R ) :-
  append(RowPfx,[Row|RowSfx],L),     
  length(RowPfx,X) ,                
  append(ColPfx,[_|ColSfx],Row) ,    
  length(ColPfx,Y) ,                 
  append(ColPfx,[Z|ColSfx],RowNew) , 
  append(RowPfx,[RowNew|RowSfx],R). 

remove_list([], _, []).
remove_list([X|Tail], L2, Result):- member(X, L2), !, remove_list(Tail, L2, Result). 
remove_list([X|Tail], L2, [X|Result]):- remove_list(Tail, L2, Result).

notDisturbExam([exam(ExamName1,StartTime1,LastTime1),exam(ExamName2,StartTime2,LastTime2)]):-
	(StartTime1 + LastTime1) =< StartTime2.
notDisturbExam([exam(ExamName1,StartTime1,LastTime1),exam(ExamName2,StartTime2,LastTime2)]):-
	(StartTime2 + LastTime2) =< StartTime1.

append([],A,A).
append([X|A],B,[X|C]):-
	append(A,B,C).

delete(X,[],[]).
delete(X, [X|Ys], Ys).
delete(X, [Y|Ys], [Y|Zs]) :-
	X \= Y,
	delete(X, Ys, Zs).

comb(_,[]).
comb([X|T],[X|Comb]):-comb(T,Comb).
comb([_|T],[X|Comb]):-comb(T,[X|Comb]).

combination(0,_,[]).
combination(K,L,[X|Xs]) :- K > 0,
   el(X,L,R), K1 is K-1, combination(K1,R,Xs).

el(X,[X|L],L).
el(X,[_|L],R) :- el(X,L,R).

combineAlllist(Timetable,Listlist):-
	findall(X,
		(combination(2,Timetable,X)
		),Listlist).

combinenotDisturblist(Timetable,Listlist):-
	findall(X,
		(combination(2,Timetable,X),
		notDisturbExam(X)
		),Listlist).

removeDup([],[]).
removeDup([H|T],[H|NewList]):-
	\+ member(H,T),
	removeDup(T,NewList).
removeDup([H|T],NewList):-
	member(H,T),
	removeDup(T,NewList).

generateEmptyGraph(Length,Graph):-
	n_matrix(Length,Graph).

length_list(N, L) :-
   length(L, N).

n_matrix(N, Graph) :-
   length(Graph, N),
   maplist(N,Graph).

maplist(_, []).
maplist(C,[X|Xs]) :-
	build(C,X),
  	maplist(C, Xs).

build(0,[]).
build(C,[H|T]):-
	C > 0->
	H is 0,
	C1 is C-1,
	build(C1,T).

schedule_time(Graph, KColors, Coloring) :-
    clique_find_single(Graph, MaxClique),
    writeln(MaxClique),
    encode(coloring(Graph, KColors, MaxClique), Map, Constr),
    writeln(Constr),
    bCompile(Constr, CNF),
    writeln(CNF),
    sat(CNF),
    decode(Map, Coloring).
    
encode(Instance, Map, Constr) :-
    nonvar(Instance),
    Instance = coloring(G, K, MaxClique),
    Map = vars(Vs),
    break_clique_symmetry(G, MaxClique, K, Vs, Constr1-Constr2),
    coloring_constraints(G, Vs, Constr2-Constr3),
    Constr = Constr1,
    Constr3 = [].
    
break_clique_symmetry(G, MaxClique, K, Vs, Constr1-Constr2) :-
    proper_length(MaxClique, NClique),
    NClique =< K,
    proper_length(G, NVert),
    length(Vs, NVert),
    color_clique_vertices(MaxClique, 1, Vs),
    generate_remaining_vertices(Vs, K, Constr1-Constr2).
    
color_clique_vertices([], _, _).
color_clique_vertices([C|Cs], I, Vs) :-
    nth1(C, Vs, I), I1 is I+1,
    color_clique_vertices(Cs, I1, Vs).

generate_remaining_vertices([], _, Tail-Tail).
generate_remaining_vertices([V|Vs], K, Cs1-Cs3) :-
    (   var(V)
    ->  Cs1 = [new_int(V, 1, K) | Cs2]
    ;   Cs1 = Cs2
    ),
    generate_remaining_vertices(Vs, K, Cs2-Cs3).
    
coloring_constraints(G, Vs, Cs1-Cs2) :-
    findall(I-J, (nth1(I, G, Gi), nth1(J, Gi, Gij), I<J, Gij==1), Es),
    not_same_color(Es, Vs, Cs1-Cs2).
    
not_same_color([], _, Tail-Tail).
not_same_color([I-J|Es], Vs, [int_neq(Ci,Cj)|Cs1]-Cs2) :-
    nth1(I, Vs, Ci), nth1(J, Vs, Cj),
    not_same_color(Es, Vs, Cs1-Cs2).

decode(Map, Coloring) :-
    Map = vars(Vs),
    decodeIntArray(Vs, Coloring).

