% Author: Amit Metodi
% Last Updated: 17/04/2017

:- module(bSettings, []).

/*
  NOTE: BEE settings are staticly set when loading BEE.
        They can not be changed after loading BEE
        as they effect the loading process.
        It is done in order to improve efficiency (CPU and memory).
        
        To change the default settings,
        the user should use:
        :- nb_setval(bee_<NAME>,<New Value>).
        before loading BEE modules.
        
        For example:
        :- module(myApp, [...]).
        :- nb_setval(bee_unaryAdderType, hybrid).
        :- use_module('bCompiler',[bCompile/2]).
        <rest of myApp module code>
        
*/

/*
    BEE internal function.
*/
defineSetting(Name,Default):-
    atom_concat(bee_,Name,VarName),!,
    catch( nb_getval(VarName,Value),
           error(existence_error(_,_),_),
           Value=Default),!,
    dynamic(bSettings:Name/1),!,
    Setting =.. [Name,Value],
    assertz(bSettings:Setting),!,
    compile_predicates([bSettings:Name/1]),!.


% Compiler Settings
%==================

/*
  Name: 'applyAdvSimplify'
  Possible values:
  'true'  - (default) Apply Advance Simplification rules.
  'false' - Skip Advance Simplification rules.
*/
:- defineSetting(applyAdvSimplify,true).

/*
  Name: 'catchBugExceptions'
  Possible values:
  'true'  - (default) BEE will catch bug exceptions and print a bug report.
  'false' - bug exception will not be catched by BEE.
*/
:- defineSetting(catchBugExceptions,true).

/*
  Name: 'showPhasesTime'
  Possible values:
  'true'  - BEE will time and print the four solving steps.
  'false' - (default) BEE will be in silent mode.
*/
:- defineSetting(showPhasesTime,false).

/*
  Name: 'inDebugMode'
  Possible values:
  'true' - BEE will print information about the solving process.
  'false' - (default)
*/
:- defineSetting(inDebugMode,false).

% Constraints Settings
%=====================

/*
  Name: 'allDiffDecompose'
  Constraint: 'int_array_allDiff'
  Possible values:
  'dual'     - (default) use dual representation (order+direct) and
               encode the constraint on the direct representation.
  'pairwise' - decompose to O(N^2) int_neq constraints.
*/
:- defineSetting(allDiffDecompose,dual).

/*
  Name: 'unaryAdderType'
  Constraint: 'int_plus'
  Possible values:
  'uadder' - (default) use O(N^2) encoding
  'merger' - decompose to comparators O(NlogN) encoding
  'hybrid' - hybrid approach:
             BEE will decide if to decompose like merger or
             encode like uadder - based on the generated CNF size.
             NOTE: Usually a better choice than merger:
                   creates less clauses and auxiliary variables.
*/
:- defineSetting(unaryAdderType,uadder).

/*
  Name: 'unaryAdderHybrid'
  Constraint: 'int_plus' when 'unaryAdderType' is set to 'hybrid'.
  Description:
  Define the Unary Adder Hybrid Factor.
  When taking the hybrid approach BEE will decompose int_plus(A,B,C)
  as merger as long as:
  uadder(A,B,C) <= 2*uadder(A/2,B/2,C/2) + combine(A/2,B/2,C) + Factor.

  The default value of Factor is 0 - decompose in order to generate
  the least amount of clauses possible.

  Incrasing the Factor will create more clauses but less variables.
*/
:- defineSetting(unaryAdderHybrid,0).

/*
  Name: 'unaryAdderAgeBType'
  Constraint: 'int_plus' when I1>=I2 (pairwise building blocks)
  Possible values:
  'merger' - (default) decompose to comparators O(NlogN) encoding.
*/
:- defineSetting(unaryAdderAgeBType,merger).

/*
  Name: 'sumBitsDecompose'
  Constraint: 'bool_array_sum_op' / 'bool_array_pb_op'
  Possible values:
  'simple'   - (default) divide and conquer technique (ignoring weights)
  'buckets'  - split to buckets, sum each bucket
               and use linear constraints to sum buckets results.
  'pairwise' - pairwise sorting network
               NOTE: when using 'pairwise' then 'uadderAdderType'
                     and 'unaryAdderAgeBType' should have the same
                     value in order to get consistent encoding
                     (as in some cases unaryAdderAgeB will be
                     converted to unaryAdder for more optimizations).
*/
:- defineSetting(sumBitsDecompose,simple).

/* Pairwise Warning */
:- ((sumBitsDecompose(pairwise),
         unaryAdderType(AdderType),
         unaryAdderAgeBType(AdderAgeBType),
     \+ AdderType=AdderAgeBType) ->
         writeln('\n%!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!'),
         writeln('%! BEE settings WARNING !'),
         writeln('%! \'sumBitsDecompose\' is set to \'pairwise\' while '),
         writeln('%! \'uadderAdderType\' and \'unaryAdderAgeBType\' are'),
         writeln('%! not set to the same value. In some cases'),
         writeln('%! \'unaryAdderAgeB\' replaced by \'unaryAdder\' for'),
         writeln('%! better optimizations and in order to get consistent'),
         writeln('%! encoding the same value should be set !'),
         writeln('%!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n')
         ;
         true
        ).


/*
  Name: 'sumUnariesDecompose'
  Constraint: 'int_array_sum_op' / 'int_array_lin_op'
  Possible values:
  'simple'  - (default) divide and conquar technique
  'buckets' - split to buckets, sum each bucket
              and sum buckets results using tare
              
  NOTE: at the moment only relevant for "Eq" only.
*/
:- defineSetting(sumUnariesDecompose,simple).

/*
  Name: 'unaryMod2decompose'
  Constraint: 'int_mod'  when modulo = 2.
  Possible values:
  'xor'   - decompose to xor constraints on the unary number bits.
  'const' - (default) decomposing using the same decomposition
            used for any other modulo constant.
*/
:- defineSetting(unaryMod2decompose,const).

/*
  Name: 'atMostOneEncoding'
  Constraint: 'int_array_sum_leq([...],1)' (at-most-one)
  Possible values:
  'pairwise'     - (default) use O(N^2) encoding [(-Xi & -Xj)]
  'commander(K)' - Use encoding from paper:
                   "Will Klieber, Gihwon Kwon. Efficient CNF Encoding for Selecting 1 from N Objects"
                   split to parts of K bits each and encode for each part:
                   (sum(Bits) =< 1) and (sum(Bits)==1 <-> Z)
                   than encode at most one on Zs recursively.
                   K=3 - Minimize the amount of clauses (3.5n). Create variables (n/2)
                   K=8 - My prefered value :)
  'product(K)'   - use encoding from the paper:
                   "Jing-Chao Chen. A new SAT encoding of the at-most-one constraint"
                   K is the minimal size of bits which will be productize.
                   If the number of bits is smaller than K, pairwise encoding is applied.
                   K=25 - My prefered value :)
  'sumbits'      - decompose as defined in 'sumBitsDecompose' (very similar to commander(2)).
*/
:- defineSetting(atMostOneEncoding,pairwise).

/*
  Name: 'exactlyOneEncoding'
  Constraint: 'int_array_sum_eq([...],1)' (exactly-one)
  Possible values:
  'direct'       - encode At Most One (pairwise) and At Least One (single clause)
  'decompose'    - (default) encode At Most One (by setting) and At Least One (split long clause)
  'commander(K)' - Use encoding from the paper:
                   "Will Klieber, Gihwon Kwon. Efficient CNF Encoding for Selecting 1 from N Objects"
                   K=8 - My prefered value :)
*/
:- defineSetting(exactlyOneEncoding,decompose).

/*
  Name: 'vectorDiff'
  Constraint: 'bool_arrays_eq/neq/_reif(...)'
  Possible values:
  'encode'     - (default) encode the constraint with dedicated encoding
  'decompose'  - decompose to set of "xors" constraints on the array's bits
                 and "reified or" on them (old behavior).
*/
:- defineSetting(vectorDiff,encode).

/*
  Name: 'intArraysDiff'
  Constraint: 'int_arrays_eq/neq/_reif(...)'
  Possible values:
  'decomposeLink'  - (default) decompose the constraint to set of "unaryEqLinks"
                     which use "vectorDiff encoding" for better propagation.
  'decomposeDiff'  - decompose to set of "refied diff" constraints on the
                     array's ints and "reified or" on their riefs
                     (old behavior).
*/
:- defineSetting(intArraysDiff,decomposeLink).

/*
  Name: 'boolArrayEq'
  Constraint: 'bool_array_eq_reif(...)'
  Possible values:
  'simple'  - (default) Simple linear encoding.
  'arc'     - Arc-Consistent encoding.
*/
:- defineSetting(boolArrayEq,simple).

/*
  Name: 'intNotBetween'
  Constraint: 'int_not_between(...)'
  Possible values:
  'decompose'    - decompose to (A<B || A>C)
  'decomposeXor' - decompose to ((A<B) xor (C>A)) - correct only when B<=C
  'encode'       - (default) encode using dedicated encoding.
*/
:- defineSetting(intNotBetween,encode).

/*
  Name: 'useXorClauses'
  CryptoMinisat Xor Clauses:
  Possible values:
  'true'  - encode xors by using CryptoMinisat xor clauses syntax.
  'false' - (default) encode xors with regular or clauses.
*/
:- defineSetting(useXorClauses,false).