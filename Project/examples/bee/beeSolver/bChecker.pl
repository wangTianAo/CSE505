% Author: Amit Metodi
% Last Update: 05/05/2012

:- module(bChecker, [checkSolverInput/3]).
:- ['../beeCompiler/bCheck'].

checkSolverInput(Constrs,Output,Goal):-!,
   \+ \+ (
          bCheck:checkConstraints(Constrs,0),!,
          checkOutputs(Output,0),!,
          checkGoal(Goal)
         ).

checkGoal(satisfy):-!,
    writeln('valid goal.').
checkGoal(minimize(X)):-!,
    (var(X) ->
        writef('Goal: minimize must receive a defined integer (%w).\n',[X]) ;
    (X \== int ->
        writef('Goal: minimize must receive an integer (%w).\n',[X]) ;
    writef('valid goal.\n')
    )).
checkGoal(maximize(X)):-!,
    (var(X) ->
        writef('Goal: maximize must receive a defined integer (%w).\n',[X]) ;
    (X \== int ->
        writef('Goal: maximize must receive an integer (%w).\n',[X]) ;
    writef('valid goal.\n')
    )).
checkGoal(Goal):-!,
    writef('Goal: unknown goal (%w).\n',[Goal]).





checkOutputs([(_,TypeI,Xi)|Output],PI):-!,
    I is PI + 1,
    checkOuput(TypeI,Xi,I),!,
    checkOutputs(Output,I).
checkOutputs([],Cnt):-!,
    writef('%w outputs checked.\n',[Cnt]).
    
    
checkOuput(int,Xi,I):-
    (var(Xi) ->
        writef('Output #%w: undefined variable.\n',[I]) ;
    (Xi \== int ->
        writef('Output #%w: type mismatch - variable is not an integer (%w).\n',[I,Xi]) ;
    true
    )).
checkOuput(bool,Xi,I):-
    (var(Xi) ->
        writef('Output #%w: undefined variable.\n',[I]) ;
    (Xi \== bool ->
        writef('Output #%w: type mismatch - variable is not a boolean (%w).\n',[I,Xi]) ;
    true
    )).
checkOuput(int_array,Xi,I):-
    ((Xi=[] ; Xi=[_|_]) ->
        checkOuputArray(Xi,int,1,I)
    ;
        writef('Output #%w: is not an array.\n',[I])
    ).
checkOuput(bool_array,Xi,I):-
    ((Xi=[] ; Xi=[_|_]) ->
        checkOuputArray(Xi,bool,1,I)
    ;
        writef('Output #%w: is not an array.\n',[I])
    ).
checkOuput(TypeI,_,I):-!,
    writef('Output #%w: Unknown type (%w).\n',[I,TypeI]).


checkOuputArray([Xj|Xs],TypeJ,J,I):-!,
    concat_atom([I,'[',J,']'],IJ),
    checkOuput(TypeJ,Xj,IJ),!,
    J1 is J + 1,
    checkOuputArray(Xs,TypeJ,J1,I).
checkOuputArray([],_,_,_):-!.
