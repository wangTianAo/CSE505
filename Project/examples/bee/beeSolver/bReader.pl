% Author: Amit Metodi
% Last Update: 19/05/2017

:- module(bReader, [readBeeFile/2]).
:- [bDCG].
:- [aMap].

readBeeFile(Filename,BEE):-
    setup_call_cleanup(
        open(Filename,read,Stream,[alias(flatZincFile)]),
    (
    newMap(VarMap),
    addToMap(true,VarMap,new_bool(1)),
    addToMap(false,VarMap,new_bool(-1)),
    readNextLine(Line),!,
    readFlatZinc_constr(Line,VarMap,BEE)
    ),
    close(Stream)),!.

readNextLine(Line):-
    read_line_to_codes(flatZincFile,LineT),!,
    whiteSpace(LineT,RestLine),!,
    ((RestLine=[] ;  % empty line
      RestLine=[37|_] % comments
      ) ->
        readNextLine(Line)
    ;
        Line=RestLine
    ).
readNextLine([]):-!.


readFlatZinc_constr(Line,VarMap,[Constraints,Goal,Outputs]):-
    constraint(Constr,Line,_),!,
    processConstr(Constr,VarMap,Constraints-ConstraintsT,Outputs-OutputsT),!,
    readNextLine(NewLine),!,
    readFlatZinc_constr(NewLine,VarMap,[ConstraintsT,Goal,OutputsT]).
readFlatZinc_constr(Line,VarMap,[[],Goal,[]]):-
    solveGoal(GoalFZ,Line,_),!,
    processGoal(GoalFZ,VarMap,Goal).

readFlatZinc_constr(_,_,_):-!,
    line_count(flatZincFile, LineCount1),
    LineCount is LineCount1 - 1,
    writef('ERROR: while parsing line %w.\n',[LineCount]),
    !, fail.


processConstr((new_int,[VarId,Min,Max]),VarMap,[Constr|Constraints]-Constraints,[(VarId,int,Int)|Outputs]-Outputs):-!,
    Constr=new_int(Int,Min,Max),
    addToMap(VarId,VarMap,Constr).
processConstr((new_int,[VarId,Dom]),VarMap,[Constr|Constraints]-Constraints,[(VarId,int,Int)|Outputs]-Outputs):-!,
    Constr=new_int(Int,Dom),
    addToMap(VarId,VarMap,Constr).
processConstr((new_int_direct,[VarId,Min,Max]),VarMap,[Constr|Constraints]-Constraints,[(VarId,int,Int)|Outputs]-Outputs):-!,
    Constr=new_int_direct(Int,Min,Max),
    addToMap(VarId,VarMap,Constr).
processConstr((new_int_direct,[VarId,Dom]),VarMap,[Constr|Constraints]-Constraints,[(VarId,int,Int)|Outputs]-Outputs):-!,
    Constr=new_int_direct(Int,Dom),
    addToMap(VarId,VarMap,Constr).
processConstr((new_int_dual,[VarId,Min,Max]),VarMap,[Constr|Constraints]-Constraints,[(VarId,int,Int)|Outputs]-Outputs):-!,
    Constr=new_int_dual(Int,Min,Max),
    addToMap(VarId,VarMap,Constr).

processConstr((new_int_plusK,[VarId,OldVarId,K]),VarMap,[Constr|Constraints]-Constraints,[(VarId,int,Int)|Outputs]-Outputs):-!,
    replaceVarIdWithVar(OldVarId,VarMap,OldInt),
    Constr=new_int_plusK(Int,OldInt,K),
    addToMap(VarId,VarMap,Constr).
processConstr((new_int_direct_plusK,[VarId,OldVarId,K]),VarMap,[Constr|Constraints]-Constraints,[(VarId,int,Int)|Outputs]-Outputs):-!,
    replaceVarIdWithVar(OldVarId,VarMap,OldInt),
    Constr=new_int_direct_plusK(Int,OldInt,K),
    addToMap(VarId,VarMap,Constr).
processConstr((new_int_dual_plusK,[VarId,OldVarId,K]),VarMap,[Constr|Constraints]-Constraints,[(VarId,int,Int)|Outputs]-Outputs):-!,
    replaceVarIdWithVar(OldVarId,VarMap,OldInt),
    Constr=new_int_dual_plusK(Int,OldInt,K),
    addToMap(VarId,VarMap,Constr).
processConstr((new_int_mulK,[VarId,OldVarId,K]),VarMap,[Constr|Constraints]-Constraints,[(VarId,int,Int)|Outputs]-Outputs):-!,
    replaceVarIdWithVar(OldVarId,VarMap,OldInt),
    Constr=new_int_mulK(Int,OldInt,K),
    addToMap(VarId,VarMap,Constr).
processConstr((new_int_divK,[VarId,OldVarId,K]),VarMap,[Constr|Constraints]-Constraints,[(VarId,int,Int)|Outputs]-Outputs):-!,
    replaceVarIdWithVar(OldVarId,VarMap,OldInt),
    Constr=new_int_divK(Int,OldInt,K),
    addToMap(VarId,VarMap,Constr).

processConstr((new_temp_int,[VarId,Min,Max]),VarMap,[Constr|Constraints]-Constraints,Outputs-Outputs):-!,
    Constr=new_int(_Int,Min,Max),
    addToMap(VarId,VarMap,Constr).
processConstr((new_temp_int,[VarId,Dom]),VarMap,[Constr|Constraints]-Constraints,Outputs-Outputs):-!,
    Constr=new_int(_Int,Dom),
    addToMap(VarId,VarMap,Constr).
processConstr((new_temp_int_direct,[VarId,Min,Max]),VarMap,[Constr|Constraints]-Constraints,Outputs-Outputs):-!,
    Constr=new_int_direct(_Int,Min,Max),
    addToMap(VarId,VarMap,Constr).
processConstr((new_temp_int_direct,[VarId,Dom]),VarMap,[Constr|Constraints]-Constraints,Outputs-Outputs):-!,
    Constr=new_int_direct(_Int,Dom),
    addToMap(VarId,VarMap,Constr).
processConstr((new_temp_int_dual,[VarId,Min,Max]),VarMap,[Constr|Constraints]-Constraints,Outputs-Outputs):-!,
    Constr=new_int_dual(_Int,Min,Max),
    addToMap(VarId,VarMap,Constr).

processConstr((new_bool,[VarId]),VarMap,[Constr|Constraints]-Constraints,[(VarId,bool,Bool)|Outputs]-Outputs):-!,
    Constr=new_bool(Bool),
    addToMap(VarId,VarMap,Constr).

processConstr((new_temp_bool,[VarId]),VarMap,[Constr|Constraints]-Constraints,Outputs-Outputs):-!,
    Constr=new_bool(_Bool),
    addToMap(VarId,VarMap,Constr).

processConstr((ConstrId,Exprs),VarMap,[Constr|Constraints]-Constraints,Outputs-Outputs):-!,
    replaceVarIdsWithVars(Exprs,VarMap,ExprVars),
    Constr =.. [ConstrId|ExprVars].


processGoal(satisfy,_,satisfy):-!.
processGoal(satisfy(X),_,satisfy(X)):-!.
processGoal(minimize(VarId),VarMap,minimize(Var)):-!,
    getFromMap(VarId,VarMap,Value),!,
    Value=new_int(Var,_,_).
processGoal(maximize(VarId),VarMap,maximize(Var)):-!,
    getFromMap(VarId,VarMap,Value),!,
    Value=new_int(Var,_,_).


replaceVarIdsWithVars([X|Xs],VarMap,[FX|FXs]):-!,
    replaceVarIdWithVar(X,VarMap,FX),!,
    replaceVarIdsWithVars(Xs,VarMap,FXs).
replaceVarIdsWithVars([],_,[]):-!.

replaceVarIdWithVar(true,_,1):-!.
replaceVarIdWithVar(false,_,-1):-!.
replaceVarIdWithVar(X,_,X):-integer(X),!.
replaceVarIdWithVar([],_,[]):-!.
replaceVarIdWithVar([X|Xs],VarMap,FXs):-!,
    replaceVarIdsWithVars([X|Xs],VarMap,FXs).
replaceVarIdWithVar(-VarID,VarMap,-Var):-!,
    replaceVarIdWithVar(VarID,VarMap,Var).
replaceVarIdWithVar(VarID,VarMap,Var):-!,
    (getFromMap(VarID,VarMap,Value) ->
        (
         Value=new_int(Var,_,_) ;
         Value=new_bool(Var) ;
         Value=new_int(Var,_) ;
         Value=new_int_direct(Var,_,_) ;
         Value=new_int_direct(Var,_) ;
         Value=new_int_dual(Var,_,_) ;
         Value=new_int_plusK(Var,_,_) ;
         Value=new_int_direct_plusK(Var,_,_) ;
         Value=new_int_dual_plusK(Var,_,_) ;
         Value=new_int_mulK(Var,_,_) ;
         Value=new_int_divK(Var,_,_)
         )
    ;
        Constr=new_bool(Var),
        addToMap(VarID,VarMap,Constr)
    ).
