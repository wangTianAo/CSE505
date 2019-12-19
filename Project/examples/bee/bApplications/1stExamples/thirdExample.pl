% 3rd example for using BEE framework to find all solutions
% Author: Amit Metodi

:- module('thirdExample', [ solve_framework/2 ]).
% --- Step 1 --- %
% consult the Experiments Framework
:- use_module('../auxs/auxRunExprAll',[runExprAll/5, decodeIntArray/2]).

% --- Step 2 --- %
% write encode/4 predicate
% RelevantBools = list of boolean variables
% RelevantInts = list of integer varaibles
encode(Instance,Map,(RelevantBools,RelevantInts),Constraints):-
    Constraints=[new_int(A,0,Instance), new_int(B,0,Instance), int_leq(A,B)],
    Map=map([A,B]),
    RelevantBools=[],
    RelevantInts=[A,B].

% --- Step 3 --- %
% write decode/3 predicate
decode(map(Nums),Solution):-
    % use the auxiliary module to decode integers
    decodeIntArray(Nums,Solution).


% --- Step 4 --- %
% write verify/2 predicate to verified the solution
verify(Instance,Solution):-
    Solution=[A,B],
    A =< B,
    A =< Instance,
    B =< Instance.

% --- Step 5 --- %
% write solve/2 predicate which wrap runExpr predicate
solve_framework(Instance,Solutions):-
    writef('%w,',[Instance]),flush_output,
    runExprAll(Instance,Solutions,
            thirdExample:encode,
            thirdExample:decode,
            thirdExample:verify).
