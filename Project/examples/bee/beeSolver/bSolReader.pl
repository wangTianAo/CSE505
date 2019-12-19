% Author: Amit Metodi
% Last Updated: 04/06/2016

:- module(bSolReader, [bSolReader/0]).
:- use_module(dimacsSolReader).

bSolReader:-
    writef('%w\n%w\n%w\n%\n',
           ["%  \\'''/ //  BumbleBEE Solution Reader  / \\_/ \\_/ \\",
            "% -(|||)(')         (04/06/2016)        \\_/ \\_/ \\_/",
            "%   ^^^            by Amit Metodi       / \\_/ \\_/ \\"]),
    flush_output,
    current_prolog_flag(argv, Args), !,
    (Args=[_,BEEmapFile,DimacsSolFile] ->
        (\+ exists_file(DimacsSolFile) ->
            writef('\nERROR: Could not find Dimacs solution file (%w) !\n',[DimacsSolFile]) ;
        write("%  reading Dimacs solution file ... "),flush_output,
        (readDimacsFile(DimacsSolFile,SolMap) ->
            writef('done\n'),flush_output,
            SolMap=(SolStatus,SolAVL),
            (SolStatus = sat ->
                write("%  reading and decoding BEE map file ... \n"),flush_output,
                !,readAndDecodeMap(BEEmapFile, SolAVL) ;
            (SolStatus = unsat ->
                bSolveWriteUNSAT ;
            writef('\n\nERROR: Unexpected value in Dimacs solution file: "%w" !\n',[SolStatus])
            ))
        ;
            writef('\n\nERROR: Could not read Dimacs solution file (%w) !\n',[DimacsSolFile])
        ))
    ;
        bUsage
    ),
    flush_output,
    halt.

bUsage:-
    writeln('%\n% USAGE:'),
    writeln('%    BumbleSol <MAP-input-file> <DIMACS-Solution-input-file>').


readDimacsFile(File,SolMap):-!,
    dimacsSolReader:readSolFile2AVL(File,sol2numbersAVL,SolMap).

readAndDecodeMap(File, SolMap):-!,
    open(File, read, FID),!,
    readAndDecodeMap_aux(FID, SolMap),!,
    close(FID),
    writeln('----------'),
    writeln('==========').

readAndDecodeMap_aux(FID, SolMap):-!,
    read_term(FID, VarInfo, []),!,
    (VarInfo = end_bee_map ->
        true
    ;
        decodeVar(VarInfo, SolMap),!,
        readAndDecodeMap_aux(FID, SolMap)
    ).

decodeVar((Name,Type,Vars),SolMap):-!,
    writef('%w = ',[Name]),
    decodeVar_byType(Type,Vars,SolMap),!,
    nl.
decodeVar(_,_):-!.

decodeVar_byType(bool,Var,SolMap):-!,
    dimacsSolReader:getLitValFromAVL(Var,SolMap,Val),
    (Val == 1 ->
        write(true)
    ;
        write(false)
    ).
decodeVar_byType(int,Var,SolMap):-!,
    decodeInt(Var,SolMap,Val),
    write(Val).
decodeVar_byType(bool_array,Vars,SolMap):-!,
    write('['),
    decodeVar_array(Vars,SolMap,bool),
    write(']').
decodeVar_byType(int_array,Vars,SolMap):-!,
    write('['),
    decodeVar_array(Vars,SolMap,int),
    write(']').
   
decodeVar_array([],_,_):-!.
decodeVar_array([X],SolMap,Type):-!,
    decodeVar_byType(Type,X,SolMap).
decodeVar_array([X|Xs],SolMap,Type):-!,
    decodeVar_byType(Type,X,SolMap),
    write(', '),
    decodeVar_array(Xs,SolMap,Type).

decodeInt(order(min(Min),Bits),SolMap,Val):-!,
    dimacsSolReader:getLitsValsFromAVL(Bits,SolMap,Vals),!,
    decodeUnary(Vals,Min,Val).
decodeInt(direct(min(Min),Bits),SolMap,Val):-!,
    dimacsSolReader:getLitsValsFromAVL(Bits,SolMap,Vals),!,
    decodeDirect(Vals,Min,Val).

decodeUnary([B|Bs],Indx,Val):-!,
    (B =:= 1 ->
        Indx1 is Indx + 1,
        decodeUnary(Bs,Indx1,Val)
    ;
        Val=Indx
    ).
decodeUnary([],Val,Val):-!.

decodeDirect([B|Bs],Indx,Val):-!,
    (B =:= 1 ->
        Val=Indx
    ;
        Indx1 is Indx + 1,
        decodeDirect(Bs,Indx1,Val)
    ).
