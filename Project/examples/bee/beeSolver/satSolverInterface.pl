% Author: Amit Metodi
% Last Update: 05/05/2012

:- module(satSolverInterface, [
                               satSolverNewSolver/0,
                               satSolverKillSolver/0,
                               satSolverAddClause/1,
                               satSolverAddCnf/1,
                               satSolverAddXorClause/1,
                               satSolverSolve/0,
                               satSolverOtherSol/1,
                               satSolverGetBoolVal/2,
                               satSolverEnsureVarCnt/1
                               ]).

%%% NEXT LINE SHOULD BE REMOVED WHEN COMPILING TO EXECUTABLE
%:- load_foreign_library('../satsolver/pl-glucose4',install).

loadSat:-
    load_foreign_library('./pl-satsolver',install).

satSolverNewSolver:-!,
    minisat_new_solver.
satSolverKillSolver:-!,
    minisat_delete_solver.
satSolverSolve:-!,
    minisat_solve.

satSolverOtherSol(OutVars):-
    createNotClause(2,OutVars,Clause),!,
    minisat_add_clause(Clause),!,
    minisat_solve.
    
createNotClause(N,N,[]):-!.
createNotClause(I,N,[X|Xs]):-!,
    minisat_get_var_assignment(I,Iasgn),
    X is -(sign(Iasgn) * I),
    I1 is I + 1,
    createNotClause(I1,N,Xs).

satSolverAddClause(X):-!,
    minisat_add_clause(X).
satSolverAddXorClause(X):-
    minisat_add_xorclause(X).

satSolverAddCnf([Clause|Clauses]):-!,
       (Clause=[x|Xs] ->
           fixClause(Xs,PureClause),
           satSolverAddXorClause(PureClause)
       ;
           fixClause(Clause,PureClause),
           satSolverAddClause(PureClause)
       ),
       satSolverAddCnf(Clauses).
satSolverAddCnf([]):-!.
    
fixClause([X|Xs],[Y|Ys]):-!,
    Y is X,
    fixClause(Xs,Ys).
fixClause([],[]):-!.

    
satSolverGetBoolVal(X,Xval):-!,
    Xi is abs(X),
    minisat_get_var_assignment(Xi,Xasgn),
    Xval is sign(Xasgn) * sign(X).
    
satSolverEnsureVarCnt(VarCnt):-!,
    minisat_nvars(CurVarCnt),
    ((CurVarCnt == VarCnt) ; (
        X is VarCnt -1,
        Y is -X,
        minisat_add_clause([X,Y])
    )),!.
