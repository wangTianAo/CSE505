% Author: Amit Metodi
% Date: 14/09/2015

:- module('auxRunExpr',
          [
            runExpr/5,
            runExprMin/5,
            runExprMax/5,
            printHeader/0,

            decodeInt/2,
            decodeIntArray/2,
            decodeIntMatrix/2
          ]).
:- use_module('../../beeCompiler/bCompiler').
:- use_module('../../satsolver/satsolver').

/*
  Usage:
  ------
  ?- runExpr(Instance,Solution,Encode,Decode,Verify)
  where:
    Encode - predicate/3: Encode(Instance,Map,Constrs)
    Decode - predicate/2: Decode(Map,Solution)
    Verify - predicate/2: Verify(Instance,Solution) - Succeed if Solution is valid solution of instance. Otherwise fail.

  ?- runExprMin(Instance,Solution,Encode,Decode,Verify)
  where:
    Encode - predicate/4: Encode(Instance,Map,MinNum,Constrs)
    Decode - predicate/2: Decode(Map,Solution)
    Verify - predicate/2: Verify(Instance,Solution) - Succeed if Solution is valid solution of instance. Otherwise fail.

  ?- runExprMax(Instance,Solution,Encode,Decode,Verify)
  where:
    Encode - predicate/4: Encode(Instance,Map,MaxNum,Constrs)
    Decode - predicate/2: Decode(Map,Solution)
    Verify - predicate/2: Verify(Instance,Solution) - Succeed if Solution is valid solution of instance. Otherwise fail.

*/


printHeader:-
    format('~|~*t~w~10+,~|~*t~w~8+,~*t~w~7+,~|~*t~w~10+,solved\n', [32,comp_time,32,clauses,32,vars,32,sat_time]),flush.

runExpr(Instance,Solution,Encode,Decode,Verify):-
    call(Encode,Instance,Map,Constraints),
    statistics(cputime,CompSTime),
    bCompile(Constraints, CNF),!,
    statistics(cputime,CompETime),
    CompTime is CompETime-CompSTime,
    format('~|~*t~5f~10+,', [32, CompTime]),flush,
    printCnfInfo(CNF),!,
    (\+ CNF=[[]] ->
        sat(CNF,Solved,SatTime),!,
        format('~|~*t~5f~10+,', [32, SatTime]),flush,
        (Solved==1 ->
            call(Decode,Map, Solution),
            (call(Verify,Instance,Solution) ->
                writeln(sat)
            ;
                writeln('WRONG')
            )
        ;
            writeln(unsat),
            Solution=unsat
        )
    ;
        format('~|~*t~5f~10+,', [32, 0.0]),flush,
        writeln(unsat('BEE')),
        Solution=unsat
    ).

runExprMin(Instance,Solution,Encode,Decode,Verify):-
    runExprMinMax(Instance,Solution,Encode,Decode,Verify,satMinUnary).
runExprMax(Instance,Solution,Encode,Decode,Verify):-
    runExprMinMax(Instance,Solution,Encode,Decode,Verify,satMaxUnary).

runExprMinMax(Instance,Solution,Encode,Decode,Verify,SatCall):-
    call(Encode,Instance,Map,MinMaxNum,Constraints),
    statistics(cputime,CompSTime),
    bCompile(Constraints, CNF),!,
    statistics(cputime,CompETime),
    CompTime is CompETime-CompSTime,
    format('~|~*t~5f~10+,', [32, CompTime]),flush,
    printCnfInfo(CNF),!,
    (\+ CNF=[[]] ->
        getUnaryBits(MinMaxNum,Bits),
        call(SatCall,CNF,Bits,Solved,SatTime),
        format('~|~*t~5f~10+,', [32, SatTime]),flush,
        (Solved==1 ->
            call(Decode,Map, Solution),
            (call(Verify,Instance,Solution) ->
                bDecode:decodeInt(MinMaxNum,MinMaxVal),
                writeln(sat(MinMaxVal))
            ;
                writeln('WRONG')
            )
        ;
            writeln(unsat),
            Solution=unsat
        )
    ;
        format('~|~*t~5f~10+,', [32, 0.0]),flush,
        writeln(unsat('BEE')),
        Solution=unsat
    ).

getUnaryBits((int,_,_,Reps),Bits):-!,
    (bcInteger:getNumberRep(Reps,order,OData) ->
        OData=(Bits,_)
    ;
        throw(runExprMinMax_err('cannot minimize/maximize an int varaible without order representation !'))
    ).


printCnfInfo(CNF):-
    length(CNF,CnfLen),
    term_variables(CNF,CNFvars),
    length(CNFvars,VarsCnt),
    format('~|~*t~w~8+,~*t~w~7+,', [32, CnfLen, 32, VarsCnt]),flush.



%%% --------------------------------- %%%
%%%    Decode Integers
%%% --------------------------------- %%%
decodeIntMatrix(M,RM):-bDecode:decodeIntMatrix(M,RM).
decodeIntArray(A,RA):-bDecode:decodeIntArray(A,RA).
decodeInt(Int,Val):-bDecode:decodeInt(Int,Val).