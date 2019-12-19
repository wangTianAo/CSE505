:- module(auxsAdjacencyMatrix,
	[ mat_create/3,
	  mat_transpose/2,
	  mat_diagonal/2,
	  map_matrix/3,
	  mat_nth1/4,
	  mat_test_set/9,
	  write_mat/2,
	  adj_matrix_create/2,
	  adj_matrix_create/3,
	  random_adj_matrix/2,
	  random_adj_matrix/3,
	  graph_edge/4,
	  graph_edges/4,
	  anti_graph/2,
	  anti_graph/3,
	  is_clique/2,
	  is_indset/2,
	  graph_greedy_indset/3,
	  graph_degree/3,
	  graph_max_degree/2,
	  graph_nodes_by_degree/3,
	  graph_neighbors/3
	]).

/**
 * matrix
 */

mat_create(Rows, Cols, Matrix) :-
	length(Matrix, Rows),
	lengths(Matrix, Cols).

lengths([],_).
lengths([R|Rs], C) :-
	length(R,C),
	lengths(Rs,C).

mat_transpose(E, []) :-
	maplist(=([]), E).
mat_transpose(Matrix, [Col|Trans]) :-
	mat_first_col(Matrix, Col, Rest),
	mat_transpose(Rest, Trans).

mat_first_col([],[],[]).
mat_first_col([[C|R]|Ms],[C|Cs],[R|Rs]) :-
	mat_first_col(Ms, Cs, Rs).

mat_diagonal([],[]).
mat_diagonal([[X|_]|Rs],[X|Xs]) :-
	mat_first_col(Rs,_,N),
	mat_diagonal(N,Xs).

map_matrix(Pred, Matrix, Map) :-
	maplist(maplist(Pred), Matrix, Map).

mat_nth1(I, J, Mat, Mij) :-
	nth1(I, Mat, Mi),
	nth1(J, Mi, Mij).

mat_test_set(Test, True, False, I, Ci, J, Cj, Mat, Mij) :-
	(once(call(Test, Ci, Cj))
	-> Value = True 
	;  Value = False),
	mat_nth1(I, J, Mat, Mij),
	Mij = Value,
	!.

write_mat([],_) :-
	!, write([]).
write_mat([A], _) :-
	!, write([A]).
write_mat([A,B|C], Space) :-
	!, write('['), write(A), write(','), nl, 
	write_mat(B,C,Space), write(']').

write_mat(A,[],Space) :-
	!, write(Space), write(A).
write_mat(A,[B|C], Space) :-
	!, write(Space), write(A), write(','), nl, 
	write_mat(B,C,Space).

/**
 * adj matrix
 */

adj_matrix_create(NVert, Matrix) :-
    adj_matrix_create(NVert, Matrix, -1).

adj_matrix_create(NVert, Matrix, DValue) :-
	mat_create(NVert, NVert, Matrix),
	mat_transpose(Matrix, Matrix),
	mat_diagonal(Matrix, Diag),
	maplist(=(DValue), Diag).
	
random_adj_matrix(N, Matrix, Edge) :-
	adj_matrix_create(N, Matrix, 0),
	term_variables(Matrix, Vars),
	maplist(random_edge(Edge), Vars).

random_edge(Pr, Var) :-
	random_float < Pr -> Var = 1 ; Var = 0.

random_adj_matrix(N, Matrix) :-
	adj_matrix_create(N, Matrix,0),
	term_variables(Matrix, Vars),
	maplist(random(0,2), Vars).

adj_matrix_to_edge_list(AdjMatrix, EdgeList) :-
	graph_edges(AdjMatrix, EdgeList).


/**
 * graph
 */
 
/*
 * **********************************************
 * graph basics:
 * **********************************************
 */
 
graph_edge(I, J, Matrix, Mij) :-
	mat_nth1(I, J, Matrix, Mij).

graph_edges(Graph, Edges) :-
    graph_edges(Graph, Edges, 1).
    
graph_edges(Graph, Edges, Value) :-
    proper_length(Graph, NVert),
    findall(I-J, 
            (between(1, NVert, I),
             between(I, NVert, J),
             I<J,
             graph_edge(I, J, Graph, Mij),
             Mij == Value),
            Edges).

% graph_edges(Edges, Graph, EdgeValue, AntiEdgeValue)
graph_edges([],Graph,_,Anti) :-
	term_variables(Graph, Vars),
	maplist(=(Anti), Vars).
graph_edges([[I,J]|Is], Graph, Edge, Anti) :-
	!, graph_edge(I, J, Graph, Gij),
	Gij = Edge,
	graph_edges(Is, Graph, Edge, Anti).
graph_edges([I-J|Is], Graph, Edge, Anti) :-
	!, graph_edge(I, J, Graph, Gij),
	Gij = Edge,
	graph_edges(Is, Graph, Edge, Anti).

/*
 * **********************************************
 * anti_graph(+Graph, ?Anti)
 * 
 * compute the complement graph, wherein (i,j)
 * is an edge iff (i,j) is not an edge in Graph
 * **********************************************
 */
anti_graph(Graph, Anti) :-
	length(Graph, NVert),
	anti_graph(NVert, Graph, Anti).

anti_graph(NVert, Graph, Anti) :-
	adj_matrix_create(NVert, Anti),
	anti_graph_(Graph, Anti).

anti_graph_([],[]).
anti_graph_([[Diag|Row]|Rows], [[Diag|AntiRow]|AntiRows]) :-
	anti_row(Row, AntiRow),
	mat_first_col(Rows, _, Rest),
	mat_first_col(AntiRows, _, AntiRest),
	anti_graph_(Rest, AntiRest).

anti_row([],[]).
anti_row([A|As], [B|Bs]) :-
	(A =:= 1
	-> B = -1
	;  B = 1),
	anti_row(As, Bs).

/*
 * **********************************************
 * is_clique(+Clique, +Graph)
 * is_indset(+IndSet, +Graph)
 * 
 * test if a subset of nodes is a clique/independent
 * set of graph.
 * **********************************************
 */
is_clique([ ], _).
is_clique([_], _).
is_clique([A,B|Clique], Graph) :-
    maplist(graph_contains_edge(Graph, A), [B|Clique]),
    is_clique([B|Clique], Graph).

graph_contains_edge(Graph, I, J) :-
    graph_edge(I, J, Graph, Gij),
    Gij == 1.

is_indset([ ], _).
is_indset([_], _).
is_indset([A,B|Cs], Graph) :-
    maplist(graph_contains_no_edge(Graph, A), [B|Cs]),
    is_indset([B|Cs], Graph).
    
graph_contains_no_edge(Graph, I, J) :-
    \+ graph_contains_edge(Graph, I, J).

/*
 * **********************************************
 * graph_greedy_indset(+VOrdering, +Graph, ?IndSet)
 * 
 * compute a maximal (but not necessarily maximum)
 * independent set of the graph given an ordering
 * of the nodes.
 * **********************************************
 */
graph_greedy_indset([], _, []).
graph_greedy_indset([V|Vs], Graph, [V|Is]) :-
    exclude(graph_contains_edge(Graph, V), Vs, Us),
    graph_greedy_indset(Us, Graph, Is).

/*
 * **********************************************
 * graph_degree(+Graph, ?Node, ?Degree)
 * graph_max_degree(+Graph, ?MaxDegree)
 * graph_nodes_by_degree(+Graph, ?Nodes, ?Degrees)
 * 
 * obtain the degree of a node / the max degree
 * of a graph / a list of nodes and their degrees
 * sorted in non increasing order.
 * **********************************************
 */
graph_degree(Graph, I, Degree) :-
    nth1(I, Graph, Row),
    include(==(1), Row, Ns),
    sumlist(Ns, Degree).

graph_max_degree(Graph, MaxDegree) :-
    proper_length(Graph, NVert),
    numlist(1, NVert, Ns),
    maplist(graph_degree(Graph), Ns, Degs),
    max_list(Degs, MaxDegree).
    
graph_nodes_by_degree(Graph, Nodes, Degrees) :-
    proper_length(Graph, NVert),
    numlist(1, NVert, Ns),
    maplist(graph_degree(Graph), Ns, Degs),
    pairs_keys_values(Pairs, Degs, Ns),
    keysort(Pairs, Sort),
    pairs_keys_values(Sort, Degrees, Nodes).

/*
 * **********************************************
 * graph_neighbors(+Vs, +Graph, ?Adj)
 * 
 * get all the vertices adjacent to the nodes
 * in Vs.
 * **********************************************
 */
graph_neighbors(Vs, Graph, Adj) :-
    graph_neighbors(Vs, Graph, Adj, Tail),
    Tail = [].

graph_neighbors([], _, Tail, Tail).
graph_neighbors([V|Vs], Graph, Adj, Tail) :-
    graph_node_neighbors(Graph, V, Adj, Mid),
    graph_neighbors(Vs, Graph, Mid, Tail).

graph_node_neighbors(Graph, I, Adj, Tail) :-
    nth1(I, Graph, Gi),
    findall(J, (nth1(J, Gi, Gij), Gij == 1), Head),
    append(Head, Tail, Adj).

