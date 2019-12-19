% Author: Amit Metodi
% Last Update: 18/06/2013

:- module('auxRunExprAll',
          [
            runExprAll/5,
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
  ?- runExprAll(Instance,Solutions,Encode,Decode,Verify)
  where:
    Encode - predicate/3: Encode(Instance,Map,(RelevantBools,RelevantInts),Constrs)
    Decode - predicate/2: Decode(Map,Solution)
    Verify - predicate/2: Verify(Instance,Solution) - Succeed if Solution is valid solution of instance. Otherwise fail.

*/


printHeader:-
    format('~|~*t~w~10+,~|~*t~w~8+,~*t~w~7+,~|~*t~w~10+,solved\n', [32,comp_time,32,clauses,32,vars,32,sat_time]),flush.

runExprAll(Instance,Solutions,Encode,Decode,Verify):-
    call(Encode,Instance,Map,RelevantVars,Constraints),
    statistics(cputime,CompSTime),
    bCompile(Constraints, CNF),!,
    statistics(cputime,CompETime),
    CompTime is CompETime-CompSTime,
    format('~|~*t~5f~10+,', [32, CompTime]),flush,
    printCnfInfo(CNF),!,
    (\+ CNF=[[]] ->
        statistics(cputime,SatStartTime),
        satsolver:minisat_new_solver,
        satsolver:minisat_add_clause([1]), % true
        (addCnf2Solver(CNF,RelevantVars,CNFVars,RelVars) ->
            getAllSolutions(CNFVars,RelVars,Decode,Map,Solutions),
            satsolver:minisat_delete_solver,
            statistics(cputime,SatEndTime),!,
            SatTime is SatEndTime-SatStartTime,
            format('~|~*t~5f~10+,', [32, SatTime]),flush,
            (Solutions=[_|_] ->
                verifySolutions(Solutions,Verify,Instance,0,0)
            ;
                writeln(unsat)
            )
		;
            satsolver:minisat_delete_solver,
            writeln(unsat)
		)
    ;
        format('~|~*t~5f~10+,', [32, 0.0]),flush,
        writeln(unsat('BEE')),
        Solutions=[]
    ).

verifySolutions([Solution|Solutions],Verify,Instance,Right,Total):-!,
    Total1 is Total + 1,
    (call(Verify,Instance,Solution) ->
        Right1 is Right + 1,
        verifySolutions(Solutions,Verify,Instance,Right1,Total1)
    ;
        verifySolutions(Solutions,Verify,Instance,Right,Total1)
    ).

verifySolutions([],_,_,Cnt,Cnt):-!,
    writeln(sat(Cnt)).
verifySolutions([],_,_,RgtCnt,TtlCnt):-
    writef('sat(%w/%w)\n',[RgtCnt,TtlCnt]).

getAllSolutions(CNFVars,RelVars,Decode, Map,Solutions):-!,
    (satsolver:minisat_solve ->
        getDecodedSolution(CNFVars,Decode,Map,Sol),!,
        Solutions=[Sol|MoreSols],
        satsolver:minisat_get_model([_|Model]),!,
        (addClause_DiffSol(Model,CNFVars,RelVars) ->
            getAllSolutions(CNFVars,RelVars,Decode, Map,MoreSols)
        ;
            MoreSols=[]
        )
    ;
        Solutions=[]
    ).


getDecodedSolution(CNFVars,Decode,Map,Sol):-
    (
        (
            (
             satsolver:minisat_assign_model([1|CNFVars]),
             call(Decode,Map,TmpSol),
             saveSolution(TmpSol)
            )
        ,fail
        )
    ;
        savedSolution(Sol)
    ).

addClause_DiffSol(Model,CNFVars,RelVars):-
    \+ \+ (
        Model=CNFVars,
        negAll(RelVars,NoAsgn),
        satsolver:minisat_add_clause(NoAsgn)
    ).

:-dynamic(savedSolution(_)).
savedSolution(none).

saveSolution(Sol):-
     retractall(auxRunExprAll:savedSolution(_)),
     asserta(auxRunExprAll:savedSolution(Sol)),!.


printCnfInfo(CNF):-
    length(CNF,CnfLen),
    term_variables(CNF,CNFvars),
    length(CNFvars,VarsCnt),
    format('~|~*t~w~8+,~*t~w~7+,', [32, CnfLen, 32, VarsCnt]),flush.
    
    
    
%%%% --- CryptoMinisat copy & paste --- %%%%
addCnf2Solver(Cnf,(RelevantBools,RelevantInts),FVars, RelVars):-
    collectIntVars(RelevantInts,IntVars),
    term_variables([RelevantBools|IntVars],RelVars),!,
    term_variables([Cnf|RelVars],FVars),!,
    (FVars = [] ->
        add_cnf_clauses(Cnf)   % in case of Cnf=[] or CNF of fixed values
    ;
        append(_,[LVar],FVars),
        \+ \+ (bind2index(FVars,2),!,
                   add_cnf_clauses(Cnf),!,
                   add_cnf_clauses([[LVar, -LVar]]))
    ).



bind2index([N|Ns],N) :- N1 is N+1, bind2index(Ns,N1).
bind2index([],_).

collectIntVars([(int,_,_,Reps)|RInts],[Bits|IntVars]):-
    collectIntVars_aux(Reps,Bits),
    collectIntVars(RInts,IntVars).
collectIntVars([],[]).

collectIntVars_aux(Reps,Bits):-!,
    (\+ (var(Reps) ; Reps == []) ->
        Reps=[(_Type,Data)|MReps],
        Bits=[Data|MData],
        collectIntVars_aux(MReps,MData)
    ;
        Bits=[]
    ).

add_cnf_clauses([Cl|Cls]):-!,
     (Cl=[x|RCl] ->
        to_minisat(RCl,MiniSatCl),
        satsolver:minisat_add_xorclause(MiniSatCl)
     ;
        to_minisat(Cl,MiniSatCl),
        satsolver:minisat_add_clause(MiniSatCl)
     ),
     add_cnf_clauses(Cls).
add_cnf_clauses([]):-!.

to_minisat([L|Ls],[N|Ns]) :-!,
    N is L,
    to_minisat(Ls,Ns).
to_minisat([],[]):-!.


negAll([V|Vs],[NV|NVs]):-!,
       NV is -(V),
       negAll(Vs,NVs).
negAll([],[]).



%%% --------------------------------- %%%
%%%    Decode Integers
%%% --------------------------------- %%%
decodeIntMatrix(M,RM):-bDecode:decodeIntMatrix(M,RM).
decodeIntArray(A,RA):-bDecode:decodeIntArray(A,RA).
decodeInt(Int,Val):-bDecode:decodeInt(Int,Val).