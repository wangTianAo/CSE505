#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "SWI-Stream.h"
#include "SWI-Prolog.h"

#include "cliquer.h"

/*
 * **********************************************
 * prolog getters/unifiers helpers
 * **********************************************
 */

/**
 * **********************************************
 * @fn pl_get_graph_from_adj_mat_ex (term_t Matrix, int sz, graph_t* output)
 * 
 * convert a prolog adjacency matrix to a cliquer
 * graph data structure.
 * **********************************************
 */
int
pl_get_graph_from_adj_mat_ex (term_t Graph, int n, graph_t *g)
{
    int c,i,j ;
    term_t mat, row, cell ;
    
    row  = PL_new_term_ref() ;
    cell = PL_new_term_ref() ;
    mat  = PL_copy_term_ref(Graph) ;
    
    for (i = 0 ; i < n ; i++) {
        if (!PL_get_list_ex(mat, row, mat))
            return FALSE ;
        
        for (j = 0 ; j < n ; j++) {
            if (!PL_get_list_ex(row, cell ,row))
                return FALSE ;
            
            if (!PL_get_integer_ex(cell, &c))
                return FALSE ;
            
            if (c == 1)
                GRAPH_ADD_EDGE(g, i, j) ;
        }
        
        if (!PL_get_nil_ex(row))
            return FALSE ;
    }
    
    if (!PL_get_nil_ex(mat))
        return FALSE ;
    
    return TRUE ;
}

/**
 * **********************************************
 * @fn pl_unify_graph_with_adj_mat (term_t Matrix, graph_t* output, int edge, int anti)
 * 
 * convert a cliquer graph data structure to a 
 * prolog adjacency matrix
 * **********************************************
 */
int
pl_unify_graph_with_adj_mat (term_t Graph, graph_t *g, int edge, int anti)
{
    int i, j, c ;
    term_t mat, row, cell ;
    
    int n = g->n ;
    mat   = PL_copy_term_ref (Graph) ;
    row   = PL_new_term_ref () ;
    cell  = PL_new_term_ref () ;
    for(i = 0 ; i < n ; i++) {
        row = PL_new_term_ref () ;
        if(!PL_unify_list (mat, row, mat)) {
            return FALSE ;
        }
        
        for(j = 0 ; j < n ; j++) {
            cell = PL_new_term_ref () ;
            if(!PL_unify_list (row, cell, row)) {
                return FALSE ;
            }
            
            c = GRAPH_IS_EDGE (g,i,j) ? edge : anti ;
            if(!PL_unify_integer (cell, c)) {
                return FALSE ;
            }
        }
        
        if(!PL_unify_nil (row)) {
            return FALSE ;
        }
    }
    
    if(!PL_unify_nil (mat)) {
        return FALSE ;
    }
    
    return TRUE ;
}

/**
 * **********************************************
 * @fn pl_get_int_array_from_list_ex (term_t List, int len, int offset, int* array)
 * 
 * convert a prolog int-list to a C int[] array
 * of length len. Each element of the list is
 * incremented by offset, and array should be
 * allocated before calling this function.
 * **********************************************
 */
int
pl_get_int_array_from_list_ex (term_t List, int length, int offset, int *array)
{
    int i ;
    term_t head, tail ;
    
    head = PL_new_term_ref  () ;
    tail = PL_copy_term_ref (List) ;
    
    for (i=0; i<length; ++i)
    {   if (!PL_get_list_ex (tail, head, tail))
            return FALSE ;
        
        if (!PL_get_integer_ex (head, array+i))
            return FALSE ;
        
        array [i] += offset ;
    }
    
    if (!PL_get_nil_ex (tail))
        return FALSE ;
    
    return TRUE ;
    
}

/**
 * **********************************************
 * @fn pl_unify_list_with_int_array (term_t List, int len, int offset, int* array)
 * 
 * convert a C int[] array of length len to a 
 * prolog list List. Each element of the list 
 * is incremented by offset.
 * **********************************************
 */
int 
pl_unify_list_with_int_array (term_t list, int length, int plus, int *array)
{
    term_t head = PL_new_term_ref () ;
    term_t tail = PL_copy_term_ref (list) ;
    
    int i ;
    for(i = 0 ; i < length ; i++) {
        head = PL_new_term_ref () ;
        if (!PL_unify_list (tail, head, tail))
            return FALSE ;
        
        if (!PL_unify_integer (head, array[i]+plus))
            return FALSE ;
    }
    
    if (!PL_unify_nil (tail))
        return FALSE ;
    
    return TRUE ;
}

/*
 * **********************************************
 * raw cliquer interface - in most cases
 * you want to use the module encapsulating these
 * calls.
 * **********************************************
 */

/**
 * **********************************************
 * @fn pl_cliquer_graph_read_dimacs_file (+File, -NVert, -AdjMatrix, -Weights)
 * 
 * read a graph from a dimacs format graph file.
 * unified NVert with number of vertices,
 * AdjMatrix with the adjacency matrix representation,
 * and weights with the weights of the vertices.
 * **********************************************
 */
foreign_t
pl_cliquer_graph_read_dimacs_file
        (term_t File, term_t NVert, 
         term_t Matrix, term_t Weights,
	 term_t Edge, term_t Anti
	)
{
    char *filename ;
    if (!PL_get_atom_chars (File, &filename)) {
	PL_instantiation_error (File) ;
	PL_fail ;
    }
    
    int edge = 1;
    if (!PL_is_variable (Edge) && !PL_get_integer_ex (Edge, &edge))
	PL_fail ;
    
    int anti = 0;
    if (!PL_is_variable (Anti) && !PL_get_integer_ex (Anti, &anti))
	PL_fail ;
    
    graph_t *graph = graph_read_dimacs_file (filename) ;
    if (graph == NULL) {
	PL_instantiation_error (File) ;
	PL_fail ;
    }
    
    if (!PL_unify_integer (NVert, graph->n)) {
	if( graph != NULL ) { graph_free (graph) ; }
	PL_instantiation_error (NVert) ;
	PL_fail ;
    }
    
    if (!pl_unify_graph_with_adj_mat (Matrix, graph, edge, anti)) {
	if( graph != NULL ) { graph_free (graph) ; }
	PL_instantiation_error (Matrix) ;
	PL_fail ;
    }
    
    if(!pl_unify_list_with_int_array (Weights, graph->n, 0, graph->weights)) {
	if( graph != NULL ) { graph_free (graph) ; }
	PL_instantiation_error (Weights) ;
	PL_fail ;
    }
    
    graph_free (graph) ;
    PL_succeed ;
}

/**
 * **********************************************
 * @fn pl_cliquer_clique_find_single
 *      (term_t NVert, term_t Graph,
 *       term_t Min, term_t Max, term_t Maximal,
 *       term_t Order, term_t Weights,
 *       term_t Clique)
 * 
 * exports the prolog predicate:
 * '$pl_cliquer_clique_find_single' (+NVert, +Graph,
 *  +Min, +Max, +Maximal, +Order, +Weights, ?Clique)
 * 
 * find a single (max) clique in Graph.
 * @param NVert   number of vertices
 * @param Graph   graph as adjacency matrix
 * @param Min     minimal weight of clique to search
 * @param Max     maximal weight of clique to search
 * @param Maximal if true then search for max cliques only
 * @param Order   a static ordering of the vertices 
 *                [pass variable for none].
 * @param Weights the weights of vertices 
 *                [pass variable for none]
 * @param Clique  the output
 * 
 * options:
 *  - min_weight      [=0]
 *  - max_weight      [=0]
 *  - maximal         [=true]
 *  - static_ordering [=NULL]
 *  - weights         [=1^n]
 * **********************************************
 */
foreign_t
pl_cliquer_clique_find_single 
    (term_t NVert, term_t Graph,
     term_t Min, term_t Max, term_t Maximal,
     term_t Order, term_t Weights,
     term_t Clique)
{
    int n ;
    if (!PL_get_integer_ex (NVert, &n) || n <= 0)
        PL_fail ;
    
    int min_weight ;
    if (!PL_get_integer_ex (Min, &min_weight))
        PL_fail ;
    
    int max_weight ;
    if (!PL_get_integer_ex (Max, &max_weight))
        PL_fail ;
    
    boolean maximal ;
    if (!PL_get_bool_ex (Maximal, &maximal))
        PL_fail ;
    
    graph_t *graph = graph_new (n) ;
    if (!pl_get_graph_from_adj_mat_ex (Graph, n, graph))
    {   graph_free (graph) ;
        PL_fail ;
    }
    
    if (!PL_is_variable (Weights) && !pl_get_int_array_from_list_ex (Weights, n, 0, graph->weights))
    {   graph_free (graph) ;
        PL_fail ;
    }
    
    int *order = NULL ;
    clique_options* opts = NULL ; 
    if (!PL_is_variable (Order))
    {   opts = (clique_options*) malloc (sizeof (clique_options)) ;
        memset (opts, 0, sizeof (opts)) ;
        order = (int*) malloc (n * sizeof (int)) ;
        if (order == NULL || !pl_get_int_array_from_list_ex (Order, n, -1, order))
        {   graph_free (graph) ;
            if (order != NULL) {free (order) ;}
            PL_fail ;
        }
        
        opts->reorder_map = order ;
    }
    
    set_t clique = clique_find_single (graph, min_weight, max_weight, maximal, opts) ;
    if (clique == NULL)
    {   graph_free (graph) ;
        if (order != NULL) {free (order) ;}
        if (opts != NULL) {free (opts) ;}
        PL_fail ;
    }
    
    // Sprintf ("set is: ") ;
    set_print (clique) ;
    
    term_t head, tail ;
    int i ;
    int length = clique [-1] ;
    
    head = PL_new_term_ref ();
    tail = PL_copy_term_ref (Clique) ;
    for (i=0; i<length; ++i)
    {   if (SET_CONTAINS (clique, i))
        {   head = PL_new_term_ref () ;
            if (!PL_unify_list (tail, head, tail) || !PL_unify_integer (head, i+1))
            {   graph_free (graph) ;
                if (order != NULL) {free (order) ;}
                if (opts != NULL) {free (opts) ;}
                PL_fail ;
            }
        }
    }
    
    if (!PL_unify_nil (tail))
    {   graph_free (graph) ;
        if (order != NULL) {free (order) ;}
        if (opts != NULL) {free (opts) ;}
        PL_fail ;
    }
    
    graph_free (graph) ;
    if (order != NULL) {free (order) ;}
    if (opts != NULL) {free (opts) ;}
    PL_succeed ;
}

/*
 * forward declaration
 */
boolean print_clique (set_t, graph_t*, clique_options*) ;

/**
 * **********************************************
 * @fn pl_cliquer_clique_print_all 
 *          (term_t NVert, term_t Graph,
 *           term_t Min, term_t Max, term_t Maximal,
 *           term_t NCliques)
 * 
 * exports the prolog predicate:
 * '$cliquer_clique_print_all'/6
 * which iterates over all cliques and prints them
 * to screen.
 * 
 * @param NVert    number of vertices
 * @param Graph    input graph
 * @param Min      minimal clique to find
 * @param Max      maximal clique to find
 * @param Maximal  if true print only max cliques
 * @param NCliques number of found cliques
 * **********************************************
 */

foreign_t
pl_cliquer_clique_print_all
    (term_t NVert, term_t Graph,
     term_t Min, term_t Max, term_t Maximal,
     term_t NCliques)
{
    int n ;
    if(!PL_get_integer_ex( NVert, &n ) || n <= 0)
        PL_fail ;
    
    int min_weight ;
    if(!PL_get_integer_ex( Min, &min_weight ) )
        PL_fail ;
    
    int max_weight ;
    if(!PL_get_integer_ex( Max, &max_weight ) )
        PL_fail ;
    
    boolean maximal ;
    if(!PL_get_bool_ex(Maximal, &maximal))
        PL_fail ;
    
    graph_t *graph = graph_new( n ) ;
    if( !pl_get_graph_from_adj_mat_ex( Graph, n, graph ) ) {
        graph_free( graph ) ;
        PL_fail ;
    }
    
    clique_options opts ;
    memset (&opts, 0, sizeof (opts)) ;
    opts.user_function = &print_clique ;
    
    int ncliques = clique_find_all (graph, min_weight, max_weight, maximal, &opts) ;
    if (!PL_unify_integer (NCliques, ncliques)) {   
        graph_free (graph) ;
        PL_fail ;
    }
    
    graph_free (graph) ;
    PL_succeed ;
}

boolean
print_clique (set_t clique, graph_t* graph, clique_options* opts)
{   
    int i ;
    
    i=set_return_next (clique, -1) ;
    if (i < 0) {
        Sfprintf (Suser_error, "plclique error: found empty clique in '$cliquer_clique_print_all'/6\n") ;
        return FALSE ;
    }
    
    Sfprintf (Scurrent_output, "[%d", i+1) ;
    while ((i=set_return_next (clique, i)) >= 0) {
        Sfprintf (Scurrent_output, ", %d", i+1) ;
    }
    Sfprintf(Scurrent_output, "]\n") ;
    return TRUE ;
}

/*
 * forward declaration
 */
boolean found_clique (set_t, graph_t*, clique_options*) ;

/**
 * **********************************************
 * @fn pl_cliquer_clique_find_n_sols
 *      (term_t NVert, term_t Graph,
 *       term_t Min, term_t Max, term_t Maximal,
 *       term_t Order, term_t Weights,
 *       term_t NCliques, term_t Cliques, term_t Total)
 * 
 * this function exports the predicate:
 * '$cliquer_clique_find_n_sols'/10
 * which is a gateway to find n cliques in the
 * graph.
 * 
 * find n cliques in the graph.
 * @param NVert   number of vertices
 * @param Graph   graph as adjacency matrix
 * @param Min     minimal weight of clique to search
 * @param Max     maximal weight of clique to search
 * @param Maximal if true then search for max cliques only
 * @param Order   a static ordering of the vertices 
 *                [pass variable for none].
 * @param Weights the weights of vertices 
 *                [pass variable for none]
 * @param NCliques number of cliques to be found
 * @param Cliques  the cliques that were found
 * @param Total    the length of Cliques
 * 
 * 
 * **********************************************
 */
foreign_t
pl_cliquer_clique_find_n_sols
    (term_t NVert, term_t Graph,
     term_t Min, term_t Max, term_t Maximal,
     term_t Order, term_t Weights,
     term_t NCliques, term_t Cliques, term_t Total)
{
    int n ;
    if(!PL_get_integer_ex( NVert, &n ) || n <= 0)
	PL_fail ;
    
    int min_weight ;
    if(!PL_get_integer_ex( Min, &min_weight ) )
	PL_fail ;
    
    int max_weight ;
    if(!PL_get_integer_ex( Max, &max_weight ) )
	PL_fail ;
    
    boolean maximal ;
    if(!PL_get_bool_ex(Maximal, &maximal))
	PL_fail ;
    
    int ncliques ;
    if (!PL_get_integer_ex (NCliques, &ncliques))
        PL_fail ;
    
    graph_t *graph = graph_new( n ) ;
    if( !pl_get_graph_from_adj_mat_ex( Graph, n, graph ) ) {
	graph_free( graph ) ;
	PL_fail ;
    }
    
    if (!PL_is_variable (Weights) && !pl_get_int_array_from_list_ex (Weights, n, 0, graph->weights))
    {   graph_free (graph) ;
        PL_fail ;
    }
    
    clique_options opts ;
    memset (&opts, 0, sizeof (opts)) ;
    
    opts.user_data = malloc (sizeof (int)) ;
    * ((int*) opts.user_data) = 0 ;
    opts.user_function = &found_clique ;
    
    set_t *clique_list = (set_t *) malloc (ncliques * sizeof (set_t)) ;
    if (!clique_list) 
    {   graph_free (graph) ;
        PL_fail ;
    }
    
    opts.clique_list = clique_list ;
    opts.clique_list_length = ncliques ;
    
    int *order = NULL ;
    if (!PL_is_variable (Order))
    {   order = (int*) malloc (n * sizeof (int)) ;
        if (order == NULL || !pl_get_int_array_from_list_ex (Order, n, -1, order))
        {   graph_free (graph) ;
            if (order != NULL) {free (order) ;}
            if (clique_list != NULL) {free (clique_list) ;}
            PL_fail ;
        }
        opts.reorder_map = order ;
    }
    
    int total = clique_find_all (graph, min_weight, max_weight, maximal, &opts) ;
//     Sprintf("total: %d\n", total) ;
    
    if (!PL_unify_integer(Total, total)) {
        free (opts.clique_list) ;
        if (order != NULL) free (order) ;
        graph_free (graph) ;
        PL_fail ;
    }
    
    
    term_t current = PL_new_term_ref () ;
    term_t cliques = PL_copy_term_ref (Cliques) ;
    term_t vertex  = PL_new_term_ref () ;
    
    int j ;
    for (j=0; j<total; ++j) {
        set_t clique = opts.clique_list [j] ;
        int i, value ;
        int length = clique [-1] ;
        
        current = PL_new_term_ref () ;
        if(!PL_unify_list(cliques, current, cliques)) {
            graph_free (graph) ;
            free (opts.clique_list) ;
            if (order != NULL) free (order) ;
            PL_fail ;
        }
        
        for (i=0; i<length; ++i) {
            if (SET_CONTAINS (clique, i)) {
                vertex = PL_new_term_ref () ;
                if (!PL_unify_list (current, vertex, current)) {
                    graph_free (graph) ;
                    free (opts.clique_list) ;
                    if (order != NULL) free (order) ;
                    PL_fail ;
                }
                
                if(!PL_unify_integer (vertex, i+1)) {
                    graph_free (graph) ;
                    free (opts.clique_list) ;
                    if (order != NULL) free (order) ;
                    PL_fail ;
                }
            }
        }
        if (!PL_unify_nil (current)) {
            graph_free (graph) ;
            free (opts.clique_list) ;
            if (order != NULL) free (order) ;
            PL_fail ;
        }
    }
    
    if (!PL_unify_nil (cliques)) {
        free (opts.clique_list) ;
        opts.clique_list = NULL ;
        if (order != NULL) free (order) ;
        graph_free (graph) ;
        PL_fail ;
    }
    
    free (opts.clique_list) ;
    if (order != NULL) free (order) ;
    opts.clique_list = NULL ;
    graph_free (graph) ;
    PL_succeed ;
}

boolean found_clique (set_t clique, graph_t* graph, clique_options* opts)
{   (*((int*) opts->user_data))++ ;
    return *((int*) opts->user_data) < opts->clique_list_length ;
}

//=============================================================================
static const PL_extension predicates[] = 
{
    //
    //  { "name", arity, function, PL_FA_<flags> },
    //
    {"$cliquer_graph_read_dimacs_file",  6, (void*) pl_cliquer_graph_read_dimacs_file, 0},
    {"$cliquer_clique_find_single"    ,  8, (void*) pl_cliquer_clique_find_single    , 0},
    {"$cliquer_clique_print_all"      ,  6, (void*) pl_cliquer_clique_print_all      , 0},
    {"$cliquer_clique_find_n_sols"    , 10, (void*) pl_cliquer_clique_find_n_sols    , 0},
    #ifdef PL_CLIQUER_DEBUG
    #endif
    {NULL                             ,  0, NULL                                     , 0}    // terminating line
};

//-----------------------------------------------------------------------------
install_t install()
{
    PL_register_extensions(predicates);	/* This is the only PL_ call allowed */
    /* before PL_initialise().  It */
    /* ensures the foreign predicates */
    /* are available before loading */
    /* Prolog code */
}

































/*


foreign_t
pl_clique_find_single(term_t NVert, term_t Graph, term_t Min, term_t Max, term_t Maximal, term_t Clique)
{
    
    
    
    set_t clique = clique_find_single(graph, min_weight, max_weight, maximal, NULL) ;
    if(clique == NULL)
    {   graph_free (graph) ;
	PL_fail ;
    }
    
    Sprintf("set is: ") ;
    set_print( clique ) ;
    
    
    term_t head = PL_new_term_ref() ;
    term_t tail = PL_copy_term_ref( Clique ) ;
    
    int i, value ;
    int length = set_size( clique ) ;
    length = clique[-1] ;
    for( i = 0 ; i < length ; i++ ) {
	head = PL_new_term_ref() ;
	if(!PL_unify_list( tail, head, tail )) {
            graph_free (graph) ;
	    PL_fail ;
	}
	
	value = SET_CONTAINS(clique, i) ? i+1 : -(i+1) ;
	if(!PL_unify_integer(head, value)) {
            graph_free (graph) ;
	    PL_fail ;
        }
    }
    
    if(!PL_unify_nil(tail)) {
        graph_free (graph) ;
	PL_fail ;
    }
    
    graph_free (graph) ;
    PL_succeed ;
}*/



// foreign_t
// pl_cliquer_graph_read_dimacs_file(term_t File, term_t NVert, term_t Matrix, term_t Weights)
// {
//     char *filename ;
//     if(!PL_get_atom_chars(File, &filename)) {
// 	PL_instantiation_error(File) ;
// 	PL_fail ;
//     }
//     
//     graph_t *graph = graph_read_dimacs_file( filename ) ;
//     if(graph == NULL) {
// 	PL_instantiation_error(File) ;
// 	PL_fail ;
//     }
//     
//     if(!PL_unify_integer(NVert, graph->n)) {
// 	if( graph != NULL ) { graph_free( graph ) ; }
// 	PL_instantiation_error(NVert) ;
// 	PL_fail ;
//     }
//     
//     if(!pl_unify_graph_with_adj_mat(Matrix, graph)) {
// 	if( graph != NULL ) { graph_free( graph ) ; }
// 	PL_instantiation_error(Matrix) ;
// 	PL_fail ;
//     }
//     
//     if(!pl_unify_list_with_int_array (Weights, graph->n, 0, graph->weights)) {
// 	if( graph != NULL ) { graph_free( graph ) ; }
// 	PL_instantiation_error(Weights) ;
// 	PL_fail ;
//     }
//     
//     graph_free( graph ) ;
//     PL_succeed ;
// }
/*
foreign_t
pl_clique_find_single(term_t NVert, term_t Graph, term_t Min, term_t Max, term_t Maximal, term_t Clique)
{
    int n ;
    if(!PL_get_integer_ex( NVert, &n ) || n <= 0)
	PL_fail ;
    
    int min_weight ;
    if(!PL_get_integer_ex( Min, &min_weight ) )
	PL_fail ;
    
    int max_weight ;
    if(!PL_get_integer_ex( Max, &max_weight ) )
	PL_fail ;
    
    boolean maximal ;
    if(!PL_get_bool_ex(Maximal, &maximal))
	PL_fail ;
    
    graph_t *graph = graph_new( n ) ;
    if( !pl_get_graph_from_adj_mat_ex( Graph, n, graph ) ) {
	graph_free( graph ) ;
	PL_fail ;
    }
    
    set_t clique = clique_find_single(graph, min_weight, max_weight, maximal, NULL) ;
    if(clique == NULL)
    {   graph_free (graph) ;
	PL_fail ;
    }
    
    Sprintf("set is: ") ;
    set_print( clique ) ;
    
    
    term_t head = PL_new_term_ref() ;
    term_t tail = PL_copy_term_ref( Clique ) ;
    
    int i, value ;
    int length = set_size( clique ) ;
    length = clique[-1] ;
    for( i = 0 ; i < length ; i++ ) {
	head = PL_new_term_ref() ;
	if(!PL_unify_list( tail, head, tail )) {
            graph_free (graph) ;
	    PL_fail ;
	}
	
	value = SET_CONTAINS(clique, i) ? i+1 : -(i+1) ;
	if(!PL_unify_integer(head, value)) {
            graph_free (graph) ;
	    PL_fail ;
        }
    }
    
    if(!PL_unify_nil(tail)) {
        graph_free (graph) ;
	PL_fail ;
    }
    
    graph_free (graph) ;
    PL_succeed ;
}*/

// boolean pl_clique_print_clique (set_t clique, graph_t* graph, clique_options* opts)
// {   
//     int i=-1;
//     while ((i=set_return_next (clique, i)) >= 0) {
//         Sfprintf (Scurrent_output, "%d ", i) ;
//     }
//     Sfprintf(Scurrent_output, "\n") ;
//     return TRUE ;
// }
// 
// foreign_t
// pl_clique_print_all(term_t NVert, term_t Graph, term_t Min, term_t Max, term_t Maximal, term_t NCliques)
// {
//     int n ;
//     if(!PL_get_integer_ex( NVert, &n ) || n <= 0)
// 	PL_fail ;
//     
//     int min_weight ;
//     if(!PL_get_integer_ex( Min, &min_weight ) )
// 	PL_fail ;
//     
//     int max_weight ;
//     if(!PL_get_integer_ex( Max, &max_weight ) )
// 	PL_fail ;
//     
//     boolean maximal ;
//     if(!PL_get_bool_ex(Maximal, &maximal))
// 	PL_fail ;
//     
//     graph_t *graph = graph_new( n ) ;
//     if( !pl_get_graph_from_adj_mat_ex( Graph, n, graph ) ) {
// 	graph_free( graph ) ;
// 	PL_fail ;
//     }
//     
//     clique_options opts ;
//     memset (&opts, 0, sizeof (opts)) ;
//     opts.user_function = &pl_clique_print_clique ;
//     
//     int ncliques = clique_find_all (graph, min_weight, max_weight, maximal, &opts) ;
//     if (!PL_unify_integer (NCliques, ncliques)) {   
//         graph_free (graph) ;
//         PL_fail ;
//     }
//     
//     graph_free (graph) ;
//     PL_succeed ;
// }

// boolean pl_clique_found_clique (set_t clique, graph_t* graph, clique_options* opts)
// {   (*((int*) opts->user_data))++ ;
// //     Sprintf("found: %d\n", *((int*) opts->user_data)) ;
//     return *((int*) opts->user_data) < opts->clique_list_length ;
// }
// 
// foreign_t
// pl_clique_find_n_cliques(term_t NVert, term_t Graph, term_t Min, term_t Max, term_t Maximal, term_t NCliques, term_t Cliques, term_t Total)
// {
//     int n ;
//     if(!PL_get_integer_ex( NVert, &n ) || n <= 0)
// 	PL_fail ;
//     
//     int min_weight ;
//     if(!PL_get_integer_ex( Min, &min_weight ) )
// 	PL_fail ;
//     
//     int max_weight ;
//     if(!PL_get_integer_ex( Max, &max_weight ) )
// 	PL_fail ;
//     
//     boolean maximal ;
//     if(!PL_get_bool_ex(Maximal, &maximal))
// 	PL_fail ;
//     
//     int ncliques ;
//     if (!PL_get_integer_ex (NCliques, &ncliques))
//         PL_fail ;
//     
//     graph_t *graph = graph_new( n ) ;
//     if( !pl_get_graph_from_adj_mat_ex( Graph, n, graph ) ) {
// 	graph_free( graph ) ;
// 	PL_fail ;
//     }
//     
//     clique_options opts ;
//     memset (&opts, 0, sizeof (opts)) ;
//     
//     opts.user_data = malloc (sizeof (int)) ;
//     * ((int*) opts.user_data) = 0 ;
//     opts.user_function = &pl_clique_found_clique ;
//     
//     set_t *clique_list = (set_t *) malloc (ncliques * sizeof (set_t)) ;
//     if (!clique_list) 
//     {   graph_free (graph) ;
//         PL_fail ;
//     }
//     
//     opts.clique_list = clique_list ;
//     opts.clique_list_length = ncliques ;
//     
//     int total = clique_find_all (graph, min_weight, max_weight, maximal, &opts) ;
// //     Sprintf("total: %d\n", total) ;
//     
//     if (!PL_unify_integer(Total, total)) {
//         free(opts.clique_list) ;
//         graph_free (graph) ;
//         PL_fail ;
//     }
//     
//     
//     term_t current = PL_new_term_ref () ;
//     term_t cliques = PL_copy_term_ref (Cliques) ;
//     term_t vertex  = PL_new_term_ref () ;
//     
//     int j ;
//     for (j=0; j<total; ++j) {
//         set_t clique = opts.clique_list [j] ;
//         int i, value ;
//         int length = clique [-1] ;
//         
//         current = PL_new_term_ref () ;
//         if(!PL_unify_list(cliques, current, cliques)) {
//             graph_free (graph) ;
//             free (opts.clique_list) ;
//             PL_fail ;
//         }
//         
//         for (i=0; i<length; ++i) {
//             if (SET_CONTAINS (clique, i)) {
//                 vertex = PL_new_term_ref () ;
//                 if (!PL_unify_list (current, vertex, current)) {
//                     graph_free (graph) ;
//                     free (opts.clique_list) ;
//                     PL_fail ;
//                 }
//                 
//                 if(!PL_unify_integer (vertex, i+1)) {
//                     graph_free (graph) ;
//                     free (opts.clique_list) ;
//                     PL_fail ;
//                 }
//             }
//         }
//         if (!PL_unify_nil (current)) {
//             graph_free (graph) ;
//             free (opts.clique_list) ;
//             PL_fail ;
//         }
//     }
//     
//     if (!PL_unify_nil (cliques)) {
//         free (opts.clique_list) ;
//         opts.clique_list = NULL ;
//         graph_free (graph) ;
//         PL_fail ;
//     }
//     
//     free (opts.clique_list) ;
//     opts.clique_list = NULL ;
//     graph_free (graph) ;
//     PL_succeed ;
// }



















// int
// pl_get_graph_from_adj_mat_ex(term_t Graph, int n, graph_t *g)
// {
// 	int c,i,j ;
// 	term_t mat, row, cell ;
// 	
// 	row  = PL_new_term_ref() ;
// 	cell = PL_new_term_ref() ;
// 	mat  = PL_copy_term_ref(Graph) ;
// 	
// 	for(i = 0 ; i < n ; i++) {
// 		if(!PL_get_list_ex(mat, row, mat))
// 			return FALSE ;
// 		
// 		for(j = 0 ; j < n ; j++) {
// 			if(!PL_get_list_ex(row, cell ,row))
// 				return FALSE ;
// 			
// 			if(!PL_get_integer_ex(cell, &c))
// 				return FALSE ;
// 			
// 			if(c == 1)
// 				GRAPH_ADD_EDGE(g, i, j) ;
// 		}
// 		
// 		if(!PL_get_nil_ex(row))
// 			return FALSE ;
// 	}
// 	
// 	if(!PL_get_nil_ex(mat))
// 		return FALSE ;
// 	
// 	return TRUE ;
// }

// int
// pl_unify_graph_with_adj_mat(term_t Graph, graph_t *g)
// {
// 	int i, j, c ;
// 	term_t mat, row, cell ;
// 	
// 	int n = g->n ;
// 	mat = PL_copy_term_ref(Graph) ;
// 	row = PL_new_term_ref() ;
// 	cell = PL_new_term_ref() ;
// 	for(i = 0 ; i < n ; i++) {
// 		row = PL_new_term_ref() ;
// 		if(!PL_unify_list(mat, row, mat)) {
// 			return FALSE ;
// 		}
// 		
// 		for(j = 0 ; j < n ; j++) {
// 			cell = PL_new_term_ref() ;
// 			if(!PL_unify_list(row, cell, row)) {
// 				return FALSE ;
// 			}
// 			
// 			c = GRAPH_IS_EDGE(g,i,j) ? 1 : 0 ;
// 			if(!PL_unify_integer(cell, c)) {
// 				return FALSE ;
// 			}
// 		}
// 		
// 		if(!PL_unify_nil(row)) {
// 			return FALSE ;
// 		}
// 	}
// 	
// 	if(!PL_unify_nil(mat)) {
// 		return FALSE ;
// 	}
// 	
// 	return TRUE ;
// }

// int 
// pl_unify_list_with_int_array_ex(term_t list, int length, int plus, int *array)
// {
// 	term_t head = PL_new_term_ref() ;
// 	term_t tail = PL_copy_term_ref(list) ;
// 	
// 	int i ;
// 	for(i = 0 ; i < length ; i++) {
// 		head = PL_new_term_ref() ;
// 		if(!PL_unify_list(tail, head, tail)) {
// 			// PL_UNIFIABLE_ERROR("pair", tail) ;
// 			return FALSE ;
// 		}
// 		
// 		if(!PL_unify_integer(head, array[i]+plus)) {
// 			// PL_UNIFIABLE_ERROR("integer", head) ;
// 			return FALSE ;
// 		}
// 	}
// 	
// 	if(!PL_unify_nil(tail)) {
// 		// PL_UNIFIABLE_ERROR("[]", tail) ;
// 		return FALSE ;
// 	}
// 	
// 	return TRUE ;
// }