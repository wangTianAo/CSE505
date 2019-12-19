% 1st example for using BEE, PL-CryptoMinisat and BEE framework
% Author: Amit Metodi

:- module('firstExample', [ solve_direct/2, solve_framework/2 ]).

/*
 In this Prolog file you will find a simple example
 of using BEE to solve a simple constraint problem
 in Prolog.

 The problem:
 for a givin (N,D,K) find N different numbers
 in the domain {1..D} such that their sum is equal to
 the constant K.

*/


% ----- Method A - Direct ----- %
% First we will use BEE and PL-CryptoMinisat directly to solve the problem.
% See the next 6 steps of Method A


% --- Method A - Step 1 --- %

% consult BEE compiler module
:- use_module('../../beeCompiler/bCompiler',[bCompile/2]).
% consult PL-CryptoMinsiat module
:- use_module('../../satsolver/satsolver',[sat/1]).


% --- Method A - Step 2 --- %
% write encode/3 predicate

encode(Instance,Map,Constraints):-
    Instance=instance(N,D,K),
    length(Nums,N),
    Map=map(Nums),
    declareNums(Nums,1,D,Constraints-C2),
    C2=[ int_array_allDiff(Nums),
         int_array_plus(Nums,K) ].

declareNums([],_,_,Cs-Cs).
declareNums([Num|Nums],LB,UB,[new_int(Num,LB,UB)|CsH]-CsT):-
    declareNums(Nums,LB,UB,CsH-CsT).

% --- Method A - Step 3 --- %
% write decode/3 predicate
decode(map(Nums),Solution):-
    % use BEE auxiliary module to decode integers
    bDecode:decodeIntArray(Nums,Solution).

% --- Method A - Step 4 --- %
% write verify/2 predicate to verify the solution

verify(Instance,Solution):-
    Instance=instance(N,D,K),
    length(Solution,N),  % length is right
    sort(Solution,Tmp),  % all different
    length(Tmp,N), 
    sumlist(Solution,K), % sum is right
    append([Min|_],[Max],Tmp), % domain is right
    Max =< D,
    Min >= 1.



% --- Method A - Step 5 --- %
% write solve/2 predicate
solve_direct(Instance,Solution):-
    encode(Instance,Map,Constraints),
    bCompile(Constraints,Cnf),
    sat(Cnf),
    decode(Map,Solution),
    (verify(Instance,Solution) -> true ; writeln(wrong)).
    

% --- Method A - Step 6 --- %
/*
  Now execute:
  ?- solve_direct(instance(5,7,20),Solution).
  Solution = [6, 2, 7, 1, 4].

  ?- solve_direct(instance(4,9,40),Solution).
  false.

  ?- solve_direct(instance(4,9,33),Solution).
  false.
*/





% ----- Method B - BEE framework ----- %
% Now we will use BEE framework to solve the problem.
% See the next 6 steps of Method B

% --- Method B - Step 1 --- %
% instead of consult BEE compiler and PL-CryptoMinsiat modules
% consult the Experiments Framework
:- use_module('../auxs/auxRunExpr',[runExpr/5, decodeIntArray/2]).


% --- Method B - Step 2 --- %
% write encode/3 predicate as in Part A

% --- Method B - Step 3 --- %
% write decode/3 predicate similar to in Part A
decode_framework(map(Nums),Solution):-
    % use the framework predicate to decode integers
    decodeIntArray(Nums,Solution).

% --- Method B - Step 4 --- %
% write verify/2 predicate as in Part A


% --- Method B - Step 5 --- %
% write solve/2 predicate which wrap runExpr predicate
solve_framework(Instance,Solution):-
    writef('%w,',[Instance]),flush_output,
    runExpr(Instance,Solution,
            firstExample:encode,
            firstExample:decode_framework,
            firstExample:verify).

% --- Method B - Step 6 --- %
/*

  Now execute:
  ?- solve_framework(instance(5,7,20),Solution).
  instance(5,7,20),   0.01563,     529,    79,   0.01563,sat
  Solution = [6, 2, 7, 1, 4].
  
  ?- solve_framework(instance(4,9,40),Solution).
  instance(4,9,40),   0.00000,       1,     0,   0.00000,unsat(BEE)
  Solution = unsat.
  
  ?- solve_framework(instance(4,9,33),Solution).
  instance(4,9,33),   0.01563,     104,    23,   0.01563,unsat
  Solution = unsat.
  
  As you can see the framework will print relevant information
  to the standard output:
  Compilation time, CNF size (clauses and variables), SAT time and status

  status can be one of the four:
  sat - the instance is satisfiable and the solution if verified.
  unsat - the instance is unsatisfiable.
  unsat(BEE) - the instance is unsatisfiable - determined by BEE.
  WRONG - a solution is found but not verified to be correct.
  
*/
