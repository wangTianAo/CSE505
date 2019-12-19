% 2nd example for using BEE, PL-CryptoMinisat and BEE framework
% Author: Amit Metodi

:- module('secondExample', [ solve_direct/2, solve_framework/2 ]).

/*
 In this Prolog file you will find a simple example
 of using BEE to solve a simple constraint problem
 in Prolog.

 The problem: CSPlib 049 - Number Partitioning

 Find a partition of the numbers 1..N into two sets A and B such that:

    a) A and B have the same cardinality
    b) sum of numbers in A = sum of numbers in B
    c) sum of squares of numbers in A = sum of squares of numbers in B 

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
    Instance = instance(N),
    N mod 2 =:= 0,
    length(BitVector,N),
    Map = map(BitVector),

    Ndiv2 is N//2,
    HalfSum is N*(N+1)//4,
    HalfSqSum is N*(N+1)*(2*N+1)//12,

    findall(I,between(1,N,I),Coefs),
    findall(Isq,(between(1,N,I),Isq is I*I), SqCoefs),
    Constraints = 
                [bool_array_sum_eq(BitVector,Ndiv2),
                 bool_array_pb_eq(Coefs, BitVector, HalfSum),
                 bool_array_pb_eq(SqCoefs, BitVector, HalfSqSum)
                ].

% --- Method A - Step 3 --- %
% write decode/3 predicate
decode(Map,Solution) :- 
        Map = map(BitVector), !,
        findall(I,nth1(I,BitVector,1), A),
        findall(J,nth1(J,BitVector,-1),B),
        Solution = sol(A,B).

% --- Method A - Step 4 --- %
% write verify/2 predicate


verify(Instance,Solution):-
    Instance=instance(N),
    Ndiv2 is N//2,
    Solution=sol(A,B),
    length(A,Ndiv2), % A and B have the same cardinality
    length(B,Ndiv2),
    sumlist(A,K),% A and B have the same sum
    sumlist(B,K),
    findall(Sq,(member(Num,A),Sq is Num*Num),ASq),
    findall(Sq,(member(Num,B),Sq is Num*Num),BSq),
    sumlist(ASq,K2),% A and B have the same sum
    sumlist(BSq,K2),
    
    K is floor(((N*(N+1))/2)/2),
    K2 is floor(((N*(N+1)*(N*2+1))/6)/2).
        


% --- Method A - Step 5 --- %
% write solve/2 predicate
solve_direct(Instance,Solution):-
    encode(Instance,Map,Constraints),
    bCompile(Constraints,Cnf),
    sat(Cnf),
    decode(Map,Solution),
    (verify(Instance,Solution) -> true ; writeln(wrong)).
    




% --- Method A - Step 6--- %
/*
  Now execute:
  ?- solve_direct(instance(7),Solution).
  false.

  ?- solve_direct(instance(8),Solution).
  Solution = sol([1, 4, 6, 7], [2, 3, 5, 8]).

  ?- solve_direct(instance(10),Solution).
  false.
*/



% ----- Method B - BEE framework ----- %
% Now we will use BEE framework to solve the problem.
% See the next 6 steps of Method B

% --- Method B - Step 1 --- %
% instead of consult BEE compiler and PL-CryptoMinsiat modules
% consult the Experiments Framework
:- use_module('../auxs/auxRunExpr',[runExpr/5]).


% --- Method B - Step 2 --- %
% write encode/3 predicate as in Part A

% --- Method B - Step 3 --- %
% write decode/3 predicate as in Part A

% --- Method B - Step 4 --- %
% write verify/2 predicate as in Part A


% --- Method B - Step 5 --- %
% write solve/2 predicate which wrap runExpr predicate
solve_framework(Instance,Solution):-
    writef('%w,',[Instance]),flush_output,
    runExpr(Instance,Solution,
            secondExample:encode,
            secondExample:decode,
            secondExample:verify).

% --- Method B - Step 6 --- %
/*

  Now execute:
  ?- solve_framework(instance(4),Solution).
  instance(4),   0.00000,       1,     0,   0.00000,unsat(BEE)
  Solution = unsat.

  ?- solve_framework(instance(8),Solution).
  instance(8),   0.00000,    9924,   136,   0.10920,sat
  Solution = sol([1, 4, 6, 7], [2, 3, 5, 8]).
  
  ?- solve_framework(instance(10),Solution).
  instance(10),   0.04414,   48099,   515,   0.50074,unsat
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
