% Author: Amit Metodi
% Last Updated: 30/08/2016

:- module(bCompiler, [bCompile/2]).
:- ['bSettings'].
:- ['bParser'].
:- ['bConstraints'].
:- ['bDecode'].

:- if(bSettings:catchBugExceptions(false)).

bCompile(Input,Output):-
   catch(compileEx(Input,Output), unsat, Output=[[]]).

:- else.

bCompile(Input,Output):-
   catch(
       catch(compileEx(Input,Output), unsat, Output=[[]]) ,
       bug(Phase,Constraint),
       (printBugException(Phase,Constraint),!, Output=[[]])
       ).

printBugException(Phase,Constraint):-
    writeln('\n---------- BUG ----------'),
    writef('Phase: %w\n',[Phase]),
    extractConstraintType(Constraint,ConstrType),
    writef('Constraint: %w\n',[ConstrType]),!,
    extractConstraintFunc(Phase,Constraint,ConstrFunc),
    writef('Function: %w\n',[ConstrFunc]),!,
    write('Constraint Data: '),!,
    printConstraintIO(Constraint),
    writeln('-------------------------').


printConstraintIO(bc(_,IO)):-!,
    writeln('['),
    prettyPrintList(IO,1).
printConstraintIO(_):-!,
    writeln(unknown).

extractConstraintType(bc([_,_,_,_,ConstrType],_),ConstrType):-!.
extractConstraintType(X,X):-!.

extractConstraintFunc(simplify,bc([Func|_],_),Func):-!.
extractConstraintFunc(simplifyAdv,bc([_,Func|_],_),Func):-!.
extractConstraintFunc(decompose,bc([_,_,Func|_],_),Func):-!.
extractConstraintFunc(encode,bc([_,_,_,Func|_],_),Func):-!.
extractConstraintFunc(_,_,unknown):-!.


prettyPrintList([X|Xs],NL):-
    \+ var(X), X=[_|_],!,
    (NL==1 ; nl),!,
    write('  '),
    writeln(X),
    prettyPrintList(Xs,1).
prettyPrintList([X|Xs],NL):-
    \+ var(X), X=(_,_), !,
    (NL==1 ; nl),!,
    write('  ('),
    write(X),
    write(')'),
    ((Xs=[], writeln(')\n]'))
     ;
     (writeln('),'), prettyPrintList(Xs,1))
    ).
prettyPrintList([X|Xs],NL):-!,
    (NL==0 ; write('  ')),!,
    write(X),
    (
     (Xs=[], writeln('\n]'))
    ;
     (write(','),prettyPrintList(Xs,0))
     ).
prettyPrintList([],_):-!,
    writeln(']').

:- endif.

:- if(bSettings:showPhasesTime(false)).

compileEx(Input,Output):-!,
    bParser:parse(Input,Bconstrs-[]),!,
    simplify(Bconstrs,normal,SimplBconstrs,_),!,
    decomposeNsimplify(SimplBconstrs,DecompBConstrs),!,
    generateCnf(DecompBConstrs,Output).

:- else.

compileEx(Input,Output):-!,
      statistics(cputime,PrsTime),
      writeln('% compiler time statistics:\n% ----------------------------'),
      write('% parser    : '),flush,
    bParser:parse(Input,Bconstrs-[]),!,
      statistics(cputime,SmpTime),
      writetime(PrsTime,SmpTime),
      write('% simplify  : '),flush,
    simplify(Bconstrs,normal,SimplBconstrs,_),!,
      statistics(cputime,DcmTime),
      writetime(SmpTime,DcmTime),
      write('% decompose : '),flush,
    decomposeNsimplify(SimplBconstrs,DecompBConstrs),!,
      statistics(cputime,CnfTime),
      writetime(DcmTime,CnfTime),
      write('% cnf       : '),flush,
    generateCnf(DecompBConstrs,Output),
      statistics(cputime,EndTime),
      writetime(CnfTime,EndTime),
      writeln('% ----------------------------'),
      write('% total     : '),
      writetime(PrsTime,EndTime).

writetime(StartTime,EndTime):-
      Time is EndTime - StartTime,
      format('~|~*t~5f~10+ secs\n', [32, Time]),flush.

:- endif.

% ##################################################################
% # Simplify Components                                            #
% ##################################################################
getSimplifyFunction(bc([Func|_],_IO),Func):-!.
getSimplifyAdvFunction(bc([_,Func|_],_IO),Func):-!.

skipSimplify(Const,Const,_):-!.

:- if(bSettings:inDebugMode(false)).

simplify_itr([Constr|Constrs],ConstrsSoFar,NewConstrs,Changed):-!,
    getSimplifyFunction(Constr,SimFunc),!,
    (call(SimFunc, Constr, NewConstr, CChanged) ; throw(bug(simplify,Constr))),!,
    Changed=CChanged,!,
    (NewConstr==none ->
        simplify_itr(Constrs, ConstrsSoFar, NewConstrs, Changed)
    ;
        simplify_itr(Constrs, [NewConstr | ConstrsSoFar], NewConstrs, Changed)
    ).
simplify_itr([],Constrs,Constrs,_):-!.

:- else.  %% :- if(bSettings:inDebugMode(false)).

simplify_itr([Constr|Constrs],ConstrsSoFar,NewConstrs,Changed):-!,
    getSimplifyFunction(Constr,SimFunc),!,
    writeln(simplify(SimFunc)),
    catch(
        call(SimFunc, Constr, NewConstr, CChanged)  ,
        Exception,
        (writeln(Exception),!, throw(bug(simplify,Constr)))
    ),
    Changed=CChanged,!,
    (var(NewConstr) ->
        writeln(undef_simplify_result(SimFunc)),!, throw(bug(simplify,Constr)) ;
    (NewConstr==none ->
        simplify_itr(Constrs, ConstrsSoFar, NewConstrs, Changed)
    ;
        simplify_itr(Constrs, [NewConstr | ConstrsSoFar], NewConstrs, Changed)
    )).
simplify_itr([],Constrs,Constrs,_):-!.

:- endif. %% :- if(bSettings:inDebugMode(false)).

:- if(bSettings:applyAdvSimplify(true)).

simplify(ConstrsOrg, CurDir, ConstrsNew, Changed):-!,
    simplify_itr(ConstrsOrg, [], RevConstrs, Changed),!,
    (Changed==1 ->
        toggleDir(CurDir,NewDir),
        simplify(RevConstrs, NewDir, ConstrsNew, _)
    ;
        simplifyAdv_itr(RevConstrs, [], NewConstrs, Changed),!,
        (Changed==1 ->
            simplify(NewConstrs, CurDir, ConstrsNew, _)
        ;
            toggleListToNormal(NewConstrs, CurDir, ConstrsNew)
        )
    ).

:- if(bSettings:inDebugMode(false)).

simplifyAdv_itr([Constr|Constrs],ConstrsSoFar,NewConstrs,Changed):-!,
    getSimplifyAdvFunction(Constr,SimFunc),!,
    (call(SimFunc, Constr, NewConstr, CChanged) ; throw(bug(simplifyAdv,Constr))),!,
    Changed=CChanged,!,
    (NewConstr==none ->
        simplifyAdv_itr(Constrs, ConstrsSoFar, NewConstrs, Changed)
    ;
        simplifyAdv_itr(Constrs, [NewConstr | ConstrsSoFar], NewConstrs, Changed)
    ).
simplifyAdv_itr([],Constrs,Constrs,_):-!.

:- else.  %% :- if(bSettings:inDebugMode(false)).

simplifyAdv_itr([Constr|Constrs],ConstrsSoFar,NewConstrs,Changed):-!,
    getSimplifyAdvFunction(Constr,SimFunc),!,
    writeln(simplifyAdv(SimFunc)),
    catch(
        call(SimFunc, Constr, NewConstr, CChanged)  ,
        Exception,
        (writeln(Exception),!, throw(bug(simplifyAdv,Constr)))
    ),
    Changed=CChanged,!,
    (var(NewConstr) ->
        writeln(undef_simplifyAdv_result(SimFunc)),!, throw(bug(simplifyAdv,Constr)) ;
    (NewConstr==none ->
        simplifyAdv_itr(Constrs, ConstrsSoFar, NewConstrs, Changed)
    ;
        simplifyAdv_itr(Constrs, [NewConstr | ConstrsSoFar], NewConstrs, Changed)
    )).
simplifyAdv_itr([],Constrs,Constrs,_):-!.

:- endif.  %% :- if(bSettings:inDebugMode(false)).

:- else. %% if(bSettings:applyAdvSimplify(true)).

simplify(ConstrsOrg, CurDir, ConstrsNew, Changed):-!,
          simplify_itr(ConstrsOrg, [], RevConstrs, Changed),!,
          toggleDir(CurDir,NewDir),
          (Changed==1 ->
               simplify(RevConstrs, NewDir, ConstrsNew, _)
          ;
               toggleListToNormal(RevConstrs, NewDir, ConstrsNew)
          ).

:- endif.  %% if(bSettings:applyAdvSimplify(true)).

% ##################################################################
% # Decompose                                                      #
% ##################################################################

decomposeNsimplify(Comps,NComps):-!,
       decompose(Comps,TComps-[],GoBack),!,
       (GoBack==1 ->
              simplify(TComps,normal,STComps,_),!,
              simplify(Comps,normal,SComps,DidSimplify),!,
              (DidSimplify==1 ->
                    decomposeNsimplify(SComps,NComps)
              ;
                    NComps=STComps
              )
       ;
              NComps=TComps
       ).



getDecomposeFunction(bc([_,_,Func|_],_IO),Func):-!.
dropDecompose(_,[]):-!.

:- if(bSettings:inDebugMode(false)).

decompose([Constr|Constrs],DCompsH-DCompsT,GoBack):-!,
    getDecomposeFunction(Constr,DcmFunc),!,
    (DcmFunc==0 ->
        DCompsH=[Constr|DCompsM],!,
        decompose(Constrs,DCompsM-DCompsT,GoBack)
    ;
        (call(DcmFunc, Constr, DComps) ; throw(bug(decompose,Constr))),!,
        simplifyNdecompose(DComps,normal,DCompsH-DCompsM,GoBack),!,
        (GoBack==1 ->
            decompose(Constrs,DCompsM-DCompsT,_)
        ;
            decompose(Constrs,DCompsM-DCompsT,GoBack)
        )
    ).
decompose([],DComps-DComps,_):-!.

:- else.  %% :- if(bSettings:inDebugMode(false)).

decompose([Constr|Constrs],DCompsH-DCompsT,GoBack):-!,
    getDecomposeFunction(Constr,DcmFunc),!,
    (DcmFunc==0 ->
        DCompsH=[Constr|DCompsM],!,
        decompose(Constrs,DCompsM-DCompsT,GoBack)
        ;
        writeln(decompose(DcmFunc)),
        catch(
            call(DcmFunc, Constr, DComps),
            Exception,
            (writeln(Exception),!, throw(bug(decompose,Constr)))
        ),!,
        simplifyNdecompose(DComps,normal,DCompsH-DCompsM,GoBack),!,
        (GoBack==1 ->
            writeln('decompose back to simplify'),
            decompose(Constrs,DCompsM-DCompsT,_)
        ;
            decompose(Constrs,DCompsM-DCompsT,GoBack)
        )
    ).
decompose([],DComps-DComps,_):-!.
    
:- endif. %%  :- if(bSettings:inDebugMode(false)).

simplifyNdecompose(Constrs,CurDir,NConstrsH-NConstrsT,GoBack):-!,
       simplify_itr(Constrs, [], RevSimConstrs, DidSimplify),!,
       toggleDir(CurDir,NewDir),!,
       (DidSimplify==1 ->
            GoBack=1,
            simplifyNdecompose(RevSimConstrs,NewDir,NConstrsH-NConstrsT,_)
       ;
            toggleListToNormal(RevSimConstrs, NewDir, SimConstrs),!,
            decompose(SimConstrs,NConstrsH-NConstrsT,GoBack)
       ).

% ##################################################################
% # Encode to CNF                                                  #
% ##################################################################
getEncodeFunction(bc([_,_,_,Func|_],_),Func):-!.

:- if(bSettings:inDebugMode(false)).

generateCnf([Constr|Constrs], Cnf):-!,
    getEncodeFunction(Constr,CnfFunc),!,
    (call(CnfFunc, Constr, Cnf-CnfM) ; throw(bug(encode,Constr))),!,
    generateCnf(Constrs, CnfM).
generateCnf([], []):-!.

generateCnf_dl([Constr|Constrs], CnfH-CnfT):-!,
    getEncodeFunction(Constr,CnfFunc),!,
    (call(CnfFunc, Constr, CnfH-CnfM) ; throw(bug(encode,Constr))),!,
    generateCnf_dl(Constrs, CnfM-CnfT).
generateCnf_dl([], Cnf-Cnf):-!.

:- else.  %% :- if(bSettings:inDebugMode(false)).

generateCnf([Constr|Constrs], Cnf):-!,
    getEncodeFunction(Constr,CnfFunc),!,
    writeln(encode(CnfFunc)),
    catch(
        call(CnfFunc, Constr, Cnf-CnfM) ,
        Exception,
        (writeln(Exception),!, throw(bug(encode,Constr)))
    ),
    generateCnf(Constrs, CnfM).
generateCnf([], []):-!.

generateCnf_dl([Constr|Constrs], CnfH-CnfT):-!,
    getEncodeFunction(Constr,CnfFunc),!,
    writeln(encode(CnfFunc)),
    catch(
        call(CnfFunc, Constr, CnfH-CnfM) ,
        Exception,
        (writeln(Exception),!, throw(bug(encode,Constr)))
    ),
    generateCnf_dl(Constrs, CnfM-CnfT).
generateCnf_dl([], Cnf-Cnf):-!.

:- endif.  %% :- if(bSettings:inDebugMode(false)).

% ##################################################################
% # List direction functions                                       #
% ##################################################################

toggleListToNormal(Comps, normal, Comps):-!.
toggleListToNormal(Comps, reverse, RevComps):-!,reverse(Comps, RevComps).
toggleListToReverse(Comps, reverse, Comps):-!.
toggleListToReverse(Comps, normal, RevComps):-!,reverse(Comps, RevComps).

toggleDir(normal, reverse):-!.
toggleDir(reverse, normal):-!.
