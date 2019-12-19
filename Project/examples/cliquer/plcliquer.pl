:- module(plcliquer,
	[ graph_read_dimacs_file/4,
	  graph_read_dimacs_file/5,
	  clique_find_single/2,
	  clique_find_single/3,
	  clique_find_single/4,
	  clique_find_single/5,
	  clique_find_multi/3,
	  clique_find_multi/4,
	  clique_find_multi/5,
	  clique_print_all/1,
	  clique_print_all/3,
	  clique_print_all/6,
	  clique_find_n_sols/3,
	  clique_find_n_sols/5,
	  clique_find_n_sols/6
	]).

:- load_foreign_library('pl-cliquer.so',install).

:- use_module(library(error)).
:- use_module(library(lists)).

/*
 * **********************************************
 * graph_read_dimacs_file(+Filename, -NVert, -Matrix, -Weights)
 * graph_read_dimacs_file(+Filename, -NVert, -Matrix, -Weights, +Opts)
 * 
 * read a dimacs file.
 * **********************************************
 */
graph_read_dimacs_file(Filename, NVert, Matrix, Weights) :-
    graph_read_dimacs_file(Filename, NVert, Matrix, Weights, []).
    
graph_read_dimacs_file(Filename, NVert, Matrix, Weights, Opts) :-
    once(memberchk(edge(Edge)     , Opts) ; Edge = 1),
    once(memberchk(non_edge(Anti), Opts) ; Anti = 0), !,
    absolute_file_name(Filename, Absolute),
    % must_be(integer, NVert),
    '$cliquer_graph_read_dimacs_file'(Absolute, NVert, Matrix, Weights, Edge, Anti).

/*
 * **********************************************
 * clique_find_single (                    +Graph, ?Clique)
 * clique_find_single (+NVert,             +Graph, ?Clique)
 * clique_find_single (+NVert,             +Graph, ?Clique, +Opts)
 * clique_find_single (+NVert, +Min, +Max, +Graph, ?Clique)
 * 
 * find a single clique in a graph.
 * 
 * options include:
 *  - min_weight(nonneg)
 *    the minimal weight allowed for a clique
 *    if max clique is desired then set min_weight
 *    to zero (default)
 *
 *  - max_weight(nonneg)
 *    the maximal weight allowed for a clique
 *    if max clique is desired then set max_weight
 *    to zero (default)
 *    
 *  - maximal(boolean)
 *    if true (default) only max cliques will be
 *    found
 *    
 *  - static_ordering(list)
 *    a permutation of the nodes [1 .. n] that
 *    determines the order in which the algorithm
 *    backtracks. this parameter highly influences
 *    the runtime of the algorithm
 *    
 *  - weights(list)
 *    a list of length NVert such that nth1(I, Weights, Wi)
 *    is the weight of vertex I. By default all
 *    weights are set to 1.
 * **********************************************
 */
clique_find_single(Graph, Clique) :-
    % must_be(list(list(integer)), Graph),
    proper_length(Graph, NVert),
    '$cliquer_clique_find_single'(NVert, Graph, 0, 0, true, _, _, Clique).

clique_find_single(NVert, Graph, Clique) :-
    must_be(integer, NVert),
    '$cliquer_clique_find_single'(NVert, Graph, 0, 0, true, _, _, Clique).
    
clique_find_single(NVert, Min, Max, Graph, Clique) :-
    must_be(integer, NVert),
    must_be(integer, Min),
    must_be(integer, Max),
    (   Min == Max,
        Max == 0
    ->  Maximal = true
    ;   Maximal = false
    ),
    '$cliquer_clique_find_single'(NVert, Graph, Min, Max, Maximal, _, _, Clique).
    
clique_find_single(NVert, Graph, Clique, Opts) :-
    once(memberchk(min_weight(Min) , Opts) ; Min = 0),
    once(memberchk(max_weight(Max) , Opts) ; Max = 0),
    once(memberchk(maximal(Maximal), Opts) ; Maximal = true),
    ignore(memberchk(static_ordering(Order), Opts)),
    ignore(memberchk(weights(Weights), Opts)),
    must_be(integer, NVert),
    must_be(integer, Min),
    must_be(integer, Max),
    must_be(boolean, Maximal),
    once(var(Order) ; must_be(list, Order)),
    once(var(Weights) ; must_be(list, Weights)), !,
    '$cliquer_clique_find_single'(NVert, Graph, Min, Max, Maximal, Order, Weights, Clique).

/*
 * **********************************************
 * clique_find_multi (+Bound,         +Graph, ?Sol       )
 * clique_find_multi (+Bound, ?NVert, +Graph, ?Sol       )
 * clique_find_multi (+Bound, ?NVert, +Graph, ?Sol, +Opts)
 * 
 * backtrack over upto Bound cliques in Graph.
 * Sol is unified with a each clique upon backtracking
 * 
 * the options to this predicate are the same as 
 * in clique_find_single/4 and may also include
 * total(Total) to obtain the total number of cliques
 * found by the search.
 * 
 * this predicate calls clique_find_n_sols/5 for 
 * reasons of efficiency
 * **********************************************
 */
clique_find_multi(Bound, Graph, Sol) :-
    clique_find_n_sols(Bound, Graph, Sols),
    member(Sol, Sols).
    
clique_find_multi(Bound, NVert, Graph, Sol) :-
    clique_find_n_sols(Bound, NVert, Graph, Sols, _),
    member(Sol, Sols).
    
clique_find_multi(Bound, NVert, Graph, Sol, Opts) :-
    ignore(memberchk(total(Total), Opts)),
    clique_find_n_sols(Bound, NVert, Graph, Sols, Total, Opts), !,
    member(Sol, Sols).

/*
 * **********************************************
 * clique_print_all(                              +Graph        )
 * clique_print_all(+NVert,                       +Graph, ?Total)
 * clique_print_all(+NVert, +Min, +Max, +Maximal, +Graph, ?Total)
 * 
 * print all the cliques of sizes between Min and
 * Max in Graph, and unify Total with the total
 * number of cliques found.
 * 
 * this predicate is aware of current_output/1 and 
 * it may therefore be redirected with with_output_to/2,
 * tell/1 etc..
 * 
 * notice that in case of error this predicate
 * prints to user_error, and fails.
 * **********************************************
 */
clique_print_all(Graph) :-
    proper_length(Graph, NVert),
    '$cliquer_clique_print_all'(NVert, Graph, 0, 0, true, _).
    
clique_print_all(NVert, Graph, Total) :-
    must_be(integer, NVert),
    '$cliquer_clique_print_all'(NVert, Graph, 0, 0, true, Total).
    
clique_print_all(NVert, Min, Max, Maximal, Graph, Total) :-
    must_be(integer, NVert),
    must_be(integer, Min),
    must_be(integer, Max),
    must_be(boolean, Maximal),
    '$cliquer_clique_print_all'(NVert, Graph, Min, Max, Maximal, Total).

/*
 * **********************************************
 * clique_find_n_sols(+MaxSols,         +Graph, ?Sols               )
 * clique_find_n_sols(+MaxSols, ?NVert, +Graph, ?Sols, ?Total       )
 * clique_find_n_sols(+MaxSols, ?NVert, +Graph, ?Sols, ?Total, +Opts)
 * 
 * find upto MaxSols cliques in Graph.
 * Sols is unified with a list of the cliques, and
 * Total is unified with the length of Sols.
 * 
 * the options to this predicate are the same as 
 * in clique_find_single/4
 * **********************************************
 */
clique_find_n_sols(NSols, Graph, Sols) :-
    proper_length(Graph, NVert),
    '$cliquer_clique_find_n_sols'(NVert, Graph, 0, 0, true, _, _, NSols, Sols, _).
    
clique_find_n_sols(NSols, NVert, Graph, Sols, Total) :-
    clique_find_n_sols(NSols, NVert, Graph, Sols, Total, []).
    
clique_find_n_sols(NSols, NVert, Graph, Sols, Total, Opts) :-
    must_be(positive_integer, NSols),
    (   var(NVert)
    ->  proper_length(Graph, NVert)
    ;   must_be(integer, NVert)
    ),
    once(memberchk(min_weight(Min) , Opts) ; Min = 0),
    once(memberchk(max_weight(Max) , Opts) ; Max = 0),
    once(memberchk(maximal(Maximal), Opts) ; Maximal = true),
    ignore(memberchk(static_ordering(Order), Opts)),
    ignore(memberchk(weights(Weights), Opts)),
    must_be(integer, NVert),
    must_be(integer, Min),
    must_be(integer, Max),
    must_be(boolean, Maximal),
    once(var(Order) ; must_be(list, Order)),
    once(var(Weights) ; must_be(list, Weights)), !,
    '$cliquer_clique_find_n_sols'(NVert, Graph, Min, Max, Maximal, 
                                  Order, Weights, NSols, Sols, Total).
