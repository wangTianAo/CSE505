:- module(coloring,
	[ graphColoring/3
	]).

:- use_module('./bee/beeCompiler/bCompiler.pl', [bCompile/2]).
:- use_module('./bee/satsolver/satsolver.pl', [sat/1]).
:- use_module('./bee/beeCompiler/bDecode.pl', [decodeIntArray/2]).
:- use_module('./cliquer/plcliquer.pl').

graphColoring(Graph, KColors, Coloring) :-
    clique_find_single(Graph, MaxClique),
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

% justTheModel(Graph, KColors, Vars, Model) :-
%     clique_find_single(Graph, MaxClique),
%     encode(coloring(Graph, KColors, MaxClique), vars(Vars), Model).






% timeof(Goal, Time) :-
%     Start is cputime,
%     once(Goal),
%     Time is cputime-Start.