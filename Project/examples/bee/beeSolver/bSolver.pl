% Author: Amit Metodi
% Last Updated: 15/06/2017

:- module(bSolver, [bSolver/0]).
:- ['../beeCompiler/bCompiler'].
:- ['bReader'].
:- ['satSolverInterface'].
:- ['bChecker'].

bSolver:-
    writef('%w\n%w\n%w\n%\n',
           ["%  \\'''/ //      BumbleBEE       / \\_/ \\_/ \\",
            "% -(|||)(')     (15/06/2017)     \\_/ \\_/ \\_/",
            "%   ^^^        by Amit Metodi    / \\_/ \\_/ \\"]),
    flush_output,
    current_prolog_flag(argv, Args),
    (Args=[_,BEEfile|MoreArgs] ->
        (exists_file(BEEfile) ->
            write("%  reading BEE file ... "),flush_output,
            (readBeeFile(BEEfile,BEEmodel) ->
                BEEmodel=[Constrs,Goal,Output],
                writef('done\n'),flush_output,
                (MoreArgs=['-check'] ->
                    write("%  Checking BEE model ... \n"),flush_output,
                    bChecker:checkSolverInput(Constrs,Goal,Output) ;
                (MoreArgs=[] ->
                    %trim_stacks,
                    write("%  load pl-satSolver ... "),flush_output,
                    satSolverInterface:loadSat,
                    %writef('done\n'),flush_output,
                    bSolve(Constrs,Output,Goal) ;
                (MoreArgs=['-dimacs',DimacsFile,MapFile] ->
                    (Goal=satisfy ; writeln('%\n% WARNING: solving goal is not satisfy.\n')),
                    bToDimacs(Constrs,Output,DimacsFile,MapFile)
                ;
                writeln('\n\nERROR: wrong usage !\n\n'),
                bUsage
                )))
            ;
                writef('\n\nERROR: Could not read BEE input file (%w) !\n',[BEEfile])
            )
        ;
            writef('\nERROR: Could not find BEE input file (%w) !\n',[BEEfile])
        )
    ;
        bUsage
    ),
    flush_output,
    halt.
bSolver:-halt.

bUsage:-
    writeln('%\n% USAGE:'),
    writeln('%    BumbleBEE <BEE-input-file> [BumbleBEE-options]'),
    writeln('%\n% OPTIONS:'),
    writeln('%  BumbleBEE options are optional and mutually exclusive.\n%'),
    writeln('%  -check'),
    writeln('%      checking BEE model syntax.'),
    writeln('%  -dimacs <DIMACS-output-file> <MAP-output-file>'),
    writeln('%      dumping a DIMACS file and a MAP file.').

bSolve(Constrs,Output,Goal):-!,
    write("%  encoding BEE model ... "),flush_output,
    (catch(bCompile2satsolver(Constrs,Output,OutVars),unsat,(!,fail)) ->
        writef('done\n%  solving CNF '),flush_output,
        bSolveResults(Goal,Output,OutVars)
    ;
        writeln('done'),
        bSolveWriteUNSAT
    ),!,
    satSolverKillSolver.

bCompile2satsolver(Constrs,Output,OutVars):-!,
    bParser:parse(Constrs,Bconstrs-[]),!,
    bCompiler:simplify(Bconstrs,normal,SimplBconstrs,_),!,
    bCompiler:decomposeNsimplify(SimplBconstrs,BasicConstrs),!,
    satSolverNewSolver,
    satSolverAddClause([1]),!,
    numberFirstOuput(Output,2,OutVars),!,
    generateCnf2solver(BasicConstrs,OutVars).

% ----- solve goal = satisfy ----- %
bSolveResults(satisfy,Output,_OutVars):-
    writef('(satisfy) ...\n'),flush_output,
    (satSolverSolve ->
        bSolveWriteResults(Output),
        bSolveWriteDONE
    ;
        bSolveWriteUNSAT
    ).

% ----- solve goal = satisfy(X) ----- %
bSolveResults(satisfy(X),Output,OutVars):-
    writef('(satisfy(%w)) ...\n',[X]),flush_output,
    (satSolverSolve ->
        bSolveWriteResults(Output),
        X1 is X - 1,
        bSolveResultsAll(X1,Output,OutVars)
    ;
        bSolveWriteUNSAT
    ).

% ----- solve goal = minimize ----- %

bSolveResults(minimize(X),Output,_OutVars):-!,
    writef('(minimize) ...\n'),flush_output,
    (satSolverSolve ->
        bSolveWriteResults(Output),
        (bcInteger:haveUnaryNumber(X) ->
            bcInteger:getUnaryNumber(X,(_,_,Bits,_)),!,
            reverse(Bits,RBits),
            bSolveResultsMin(RBits,Output)
        ;
            writef('\nERROR: minimize must be done on order encoding integer.\n'),flush_output
        )
    ;
        bSolveWriteUNSAT
    ).

% ----- solve goal = maximize ----- %

bSolveResults(maximize(X),Output,_OutVars):-!,
    writef('(maximize) ...\n'),flush_output,
    (satSolverSolve ->
        bSolveWriteResults(Output),
        (bcInteger:haveUnaryNumber(X) ->
            bcInteger:getUnaryNumber(X,(_,_,Bits,_)),!,
            auxLiterals:litNotReverseXs(Bits,NRBits),
            bSolveResultsMin(NRBits,Output)
        ;
            writef('\nERROR: maximize must be done on order encoding integer.\n'),flush_output
        )
    ;
        bSolveWriteUNSAT
    ).
    
% ----- solve goal = minimize/maximize/all auxiliary ----- %

bSolveResultsAll(0,_Output,_OutVars):-!,
    bSolveWriteDONE.
bSolveResultsAll(X,Output,OutVars):-!,
    (satSolverOtherSol(OutVars) ->
        bSolveWriteResults(Output),
        X1 is X - 1,
        bSolveResultsAll(X1,Output,OutVars)
    ;
        bSolveWriteDONE
    ).

bSolveResultsMin([X|Xs],Output):-!,
    (ground(X) ->
        satSolverGetBoolVal(X,Xval),
        (Xval== -1 ->
            bSolveResultsMin(Xs,Output)
        ;
            Xi is -X,
            ((satSolverAddClause([Xi]),!,satSolverSolve) ->
                bSolveWriteResults(Output),
                bSolveResultsMin(Xs,Output)
            ;
                bSolveWriteDONE
            )
        )
    ;
        auxLiterals:litAsgnFalse(X),
        bSolveResultsMin(Xs,Output)
    ).

bSolveResultsMin([],_):-!,
    bSolveWriteDONE.




% ##################################################################
% # Encode to CNF                                                  #
% ##################################################################
getEncodeFunction(bc([_,_,_,Func|_],_),Func):-!.

generateCnf2solver([Constr|Constrs], VarId):-!,
    getEncodeFunction(Constr,CnfFunc),!,
    (call(CnfFunc, Constr, Cnf-[]) ; throw(bug(encode,CnfFunc))),!,
    writeCnf2solver(Cnf,VarId,NVarID),!,
    generateCnf2solver(Constrs,NVarID).
generateCnf2solver([], VarId):-!,
    satSolverEnsureVarCnt(VarId).

writeCnf2solver(Cnf,VarId,NVarID):-
      term_variables(Cnf, Vars),!,
      numberOutputBits(Vars,VarId,NVarID),!,
      satSolverAddCnf(Cnf),!.

numberFirstOuput([(_Name,Type,Var)|OutputVars],CurVar,StrtVar):-!,
    numberOutputVar(Type,Var,CurVar,UpdVar),
    numberFirstOuput(OutputVars,UpdVar,StrtVar).
numberFirstOuput([],StrtVar,StrtVar):-!.

numberOutputVar(bool,Var,CurVar,UpdVar):-!,
    term_variables(Var,PBits),
    numberOutputBits(PBits,CurVar,UpdVar).
numberOutputVar(int,(int,_,_,Reps),CurVar,UpdVar):-!,
    extractIntRepsBits(Reps,Bits),
    term_variables(Bits,PBits),
    numberOutputBits(PBits,CurVar,UpdVar).
numberOutputVar(bool_array,Bits,CurVar,UpdVar):-!,
    term_variables(Bits,PBits),
    numberOutputBits(PBits,CurVar,UpdVar).
numberOutputVar(int_array,Ints,CurVar,UpdVar):-!,
    collectIntsBits(Ints,IntsBits),
    term_variables(IntsBits,PBits),
    numberOutputBits(PBits,CurVar,UpdVar).

collectIntsBits([(int,_,_,Reps)|Ints],[Bits|IntsBits]):-!,
    extractIntRepsBits(Reps,Bits),
    collectIntsBits(Ints,IntsBits).
collectIntsBits([],[]):-!.

numberOutputBits([X|Bits],CurVar,FinalVar):-!,
   X is CurVar,
   UpdVar is CurVar + 1,
   numberOutputBits(Bits,UpdVar,FinalVar).
numberOutputBits([],FinalVar,FinalVar):-!.

extractIntRepsBits([],[]):-!.
extractIntRepsBits([(_,Data)|Reps],[Data|Bits]):-!,
    extractIntRepsBits(Reps,Bits).

% ##################################################################
% # Write results                                                  #
% ##################################################################
bSolveWriteUNSAT:-!,
    writeln('=====UNSATISFIABLE=====').
bSolveWriteDONE:-!,
    writeln('==========').

bSolveWriteResults([(Name,Type,Var)|Xs]):-!,
    writef('%w = ',[Name]),
    bSolveWriteVar(Type,Var),!,
    nl,
    bSolveWriteResults(Xs).
bSolveWriteResults([]):-!,
    writeln('----------').

bSolveWriteVar(bool,Var):-!,
    satSolverGetBoolVal(Var,Val),
    (Val == 1 ->
        write(true)
    ;
        write(false)
    ).
bSolveWriteVar(int,Int):-!,
    (bcInteger:haveUnaryNumber(Int) ->
        bcInteger:getUnaryNumber(Int,(Min,_,Bits,_)),
        decodeUnaryNumber(Min,Bits,Val),!,
        write(Val) ;
    (bcInteger:haveDirectNumber(Int) ->
        bcInteger:getDirectNumber(Int,(Min,_,Bits,_)),
        decodeDirectNumber(Min,Bits,Val),!,
        write(Val) ;
    write('UNKNOWN REPRESENTATION')
    )).

bSolveWriteVar(bool_array,VarArray):-!,
    write('['),
    bSolveWriteVar_array(VarArray,bool),
    write(']').
bSolveWriteVar(int_array,VarArray):-!,
    write('['),
    bSolveWriteVar_array(VarArray,int),
    write(']').

bSolveWriteVar(Type,_Var):-!,
    writef('UNKNOWN TYPE (%w)',Type).

bSolveWriteVar_array([],_):-!.
bSolveWriteVar_array([X],Type):-!,
    bSolveWriteVar(Type,X).
bSolveWriteVar_array([X|Xs],Type):-!,
    bSolveWriteVar(Type,X),
    write(', '),
    bSolveWriteVar_array(Xs,Type).
        
        
% ########## decode ints ##########
decodeUnaryNumber(Min,[Var|Vars],Val):-
    satSolverGetBoolVal(Var,BVal),
    (BVal == 1 ->
        Min1 is Min + 1,
        decodeUnaryNumber(Min1,Vars,Val)
    ;
        Val=Min
    ).
decodeUnaryNumber(Min,[],Min):-!.

decodeDirectNumber(Min,[Var|Vars],Val):-
    satSolverGetBoolVal(Var,BVal),
    (BVal == 1 ->
        Val=Min
    ;
        Min1 is Min + 1,
        decodeUnaryNumber(Min1,Vars,Val)
    ).

        
        
% ##################################################################
% # To DIMACS                                                      #
% ##################################################################
% ---- dimacs support ---- %
bToDimacs(Constrs,Output,DimacsFile,MapFile):-!,
    writef('%w',["%  encoding BEE model ... "]),flush_output,
    (catch(bCompiler:compileEx(Constrs,Cnf),unsat,(!,fail)) ->
        writef('done\n%  writing Map file ... '),flush_output,
        !,writeMapFile(MapFile,Output,NextVar),
        writef('done\n%  writing Dimacs file ... '),flush_output,
        !,writeDimacsFile(DimacsFile,Cnf,NextVar,'DIMACS File generated by BumbleBEE'),
        writeln('done')
    ;
        writeln('done'),
        bSolveWriteUNSAT
    ).

writeMapFile(File,Output,NextVar):-
    open(File, write, Stream),!,
    writeMap_aux(Output,2,Stream,NextVar),!,
    close(Stream),!.

writeMap_aux([],NextVar,Stream,NextVar):-!,
    write(Stream,'end_bee_map.'),
    nl(Stream),!.
writeMap_aux([(Name,Type,Var)|OutputVars],CurVar,Stream,NextVar):-!,
    write(Stream, '('),
    write(Stream,Name),
    write(Stream, ','),
    write(Stream,Type),
    write(Stream, ','),flush_output(Stream),
    writeMap_var(Type,Var,Stream,CurVar,UpdVar),
    write(Stream, ').'),
    nl(Stream),!,
    writeMap_aux(OutputVars,UpdVar,Stream,NextVar).

writeMap_var(bool,Var,Stream,CurVar,NextVar):-!,
    term_variables(Var,PBits),
    numberOutputBits(PBits,CurVar,NextVar),
    FVar is Var,
    write(Stream, FVar).
writeMap_var(int,Int,Stream,CurVar,NextVar):-!,
    write_order_int(Int,Stream,CurVar,NextVar).
writeMap_var(bool_array,Bits,Stream,CurVar,NextVar):-!,
    term_variables(Bits,PBits),
    numberOutputBits(PBits,CurVar,NextVar),!,
    write_array_bits(Bits,Stream).
writeMap_var(int_array,Ints,Stream,CurVar,NextVar):-!,
    write_array_ints(Ints,Stream,CurVar,NextVar).
    
write_array_bits([],Stream):-!,
    write(Stream, '[]').
write_array_bits([B0|Bits],Stream):-!,
    write(Stream, '['),
    B0f is B0,
    write(Stream, B0f),
    write_array_bits_aux(Bits,Stream),
    write(Stream, ']').

write_array_bits_aux([Bi|Bits],Stream):-!,
    write(Stream, ','),
    Bif is Bi,
    write(Stream, Bif),
    write_array_bits_aux(Bits,Stream).
write_array_bits_aux([],_):-!.

write_order_int((int,Min,_,Reps),Stream,CurVar,UpdVar):-!,
    (bcInteger:getNumberRep(Reps,order,(UBits,_)) ->
        term_variables(UBits,PBits),
        numberOutputBits(PBits,CurVar,UpdVar),
        auxUnarynum:dropLeadingOnes(UBits,FBits,Min,FMin),
        write(Stream, 'order(min('),
        write(Stream, FMin),
        write(Stream, '),'),
        write_array_bits(FBits,Stream),
        write(Stream, ')') ;
    (bcInteger:getNumberRep(Reps,direct,(DBits,_)) ->
        term_variables(DBits,PBits),
        numberOutputBits(PBits,CurVar,UpdVar),
        auxDirectnum:dropLeadingZeros(DBits,FBits,Min,FMin),
        write(Stream, 'direct(min('),
        write(Stream, FMin),
        write(Stream, '),'),
        write_array_bits(FBits,Stream),
        write(Stream, ')');
    write(Stream,'UNKNOWN_REPRESENTATION')
    )).

write_array_ints([],Stream,CurVar,CurVar):-!,
    write(Stream, '[]').
write_array_ints([I0|Ints],CurVar,NextVar):-!,
    write(Stream, '['),
    write_order_int(I0,Stream,CurVar,UpdVar),
    write(Stream, I0),
    write_array_ints_aux(Ints,Stream,UpdVar,NextVar),
    write(Stream, ']').

write_array_ints_aux([Ii|Ints],Stream,CurVar,NextVar):-
    write(Stream, ','),
    write_order_int(Ii,Stream,CurVar,UpdVar),
    write_array_ints_aux(Ints,Stream,UpdVar,NextVar).
write_array_ints_aux([],_Stream,NextVar,NextVar):-!.

numberVariables([I|Xs],I,Cnt):-
    I1 is I + 1,
    numberVariables(Xs,I1,Cnt).
numberVariables([],I,Cnt):-Cnt is I - 1.

:- if(bSettings:useXorClauses(true)).
writeClause([x|Clause], Stream):-!,
    write(Stream, 'x'),!,
    writeClause_aux(Clause, Stream).
writeClause(Clause, Stream):-!,
    writeClause_aux(Clause, Stream).

writeClause_aux([X|Clause], Stream):-!,
    XT is X,
    write(Stream, XT),!,
    write(Stream, ' '),!,
    writeClause(Clause, Stream).
writeClause_aux([], Stream):-!,
    write(Stream, '0'),
    nl(Stream),!.
:- else.
writeClause([X|Clause], Stream):-!,
    XT is X,
    write(Stream, XT),!,
    write(Stream, ' '),!,
    writeClause(Clause, Stream).
writeClause([], Stream):-!,
    write(Stream, '0'),
    nl(Stream),!.
:-endif.

writeClauses(Stream, [Clause|Cs]):-!,
    writeClause(Clause, Stream),!,
    writeClauses(Stream, Cs).
writeClauses(_Stream, []):-!.

writeDimacsFile(File, Cnf, FirstVar, Comment):-
    term_variables(Cnf,Vars),!,
    numberVariables(Vars,FirstVar,VCnt),
    length([[1]|Cnf],CCnt),
    open(File, write, Stream),!,
    write(Stream, 'c '),
    write(Stream, Comment),
    nl(Stream),!,
    write(Stream, 'p cnf '),
    write(Stream, VCnt),
    write(Stream, ' '),
    write(Stream, CCnt),
    nl(Stream),!,
    write(Stream, '1 0'),
    nl(Stream),!,
    writeClauses(Stream, Cnf),!,
    close(Stream),!.