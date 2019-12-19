% Place N Queens on NxN board so that
% no two queens attack each other.
% Author: Amit Metodi
% Last update: 05/06/2012

:- module('nQueens', [
                nQueens/2,
                printNQueens/2
                ]).

:- use_module('../auxs/auxMatrix',[matrixCreate/3, matrixTranspose/2]).
:- use_module('../auxs/auxRunExpr',[runExpr/5]).

/*
  Usage:
  ------
  ?- Instance=30, nQueens(Instance,Solution), printNQueens(Instance,Solution).
*/

nQueens(Instance,Solution):-!,
    printInstance(Instance),
    garbage_collect,!,
    runExpr(Instance,Solution,
            nQueens:encode,
            nQueens:decode,
            nQueens:verify).

printInstance(Instance):-
    writef('%5r,',[Instance]),flush.

decode(Matrix,Matrix).

encode(N,Matrix,Comps):-
    matrixCreate(N,N,Matrix),
    matrixTranspose(Matrix,MatrixTr),!,
    nQueensComps_rows(Matrix,Comps-Comps1),
    nQueensComps_rows(MatrixTr,Comps1-Comps2),
    nQueensComps_diag(Matrix,Comps2-Comps3),
    reverse(Matrix,MatrixR),
    nQueensComps_diag(MatrixR,Comps3-[]).


nQueensComps_rows([R|Rs],[bool_array_sum_eq(R,1)|CompsH]-CompsT):-
    nQueensComps_rows(Rs,CompsH-CompsT).
nQueensComps_rows([],Comps-Comps).

nQueensComps_diag([R|Rs],CompsH-CompsT):-
    nQueensComps_diagAll([R|Rs],0,CompsH-CompsM),!,
    nQueensComps_diag1st(Rs,CompsM-CompsT).

nQueensComps_diag1st([R|Rs],[bool_array_sum_leq(D,1)|CompsH]-CompsT):-
    nQueensComps_getDiagRL([R|Rs],0,D),
    nQueensComps_diag1st(Rs,CompsH-CompsT).
nQueensComps_diag1st([],Comps-Comps):-!.

nQueensComps_diagAll(Mtrx,I,CompsH-CompsT):-
    nQueensComps_getDiagRL(Mtrx,I,D),
    (D=[_] ->
        CompsH=CompsT
    ;
        CompsH=[bool_array_sum_leq(D,1)|CompsM],
        I1 is I + 1,
        nQueensComps_diagAll(Mtrx,I1,CompsM-CompsT)
    ).
    
nQueensComps_getDiagRL([R|Rs],I,[X|Xs]):-
    nth0(I,R,X),!,
    I1 is I + 1,
    nQueensComps_getDiagRL(Rs,I1,Xs).
nQueensComps_getDiagRL(_,_,[]).



% ---------- Verify N Queens board ----------
verify(N,Matrix):-!,
    amoRows(Matrix),!,
    amoDiags(Matrix),!,
    matrixTranspose(Matrix,MatrixTr),!,
    amoRows(MatrixTr),!,
    reverse(Matrix,MatrixR),!,
    amoDiags(MatrixR),!,
    countTruesInMatrix(Matrix,Cnt),!,
    N==Cnt.

amoRows([R|Rs]):-!,
    amoRow(R),!,
    amoRows(Rs).
amoRows([]).

amoRow([X|Xs]):-!,
    ((ground(X), X=:=1) ->
        allFalses(Xs) ;
        amoRow(Xs)).
amoRow([]).

amoDiags([R|Rs]):-
    amoDiagAll([R|Rs],0),!,
    amoDiag1st(Rs).

amoDiag1st([R|Rs]):-!,
    nQueensComps_getDiagRL([R|Rs],0,D),!,
    amoRow(D),!,
    amoDiag1st(Rs).
amoDiag1st([]):-!.

amoDiagAll(Mtrx,I):-!,
    nQueensComps_getDiagRL(Mtrx,I,D),!,
    (D=[_] ->
        true
    ;
        amoRow(D),!,
        I1 is I + 1,
        amoDiagAll(Mtrx,I1)
    ).

allFalses([X|Xs]):-!, ground(X), X=:= -1, allFalses(Xs).
allFalses([]).


countTruesInMatrix(Matrix,Cnt):-
    countTruesInMatrix(Matrix,0,Cnt).
    
countTruesInMatrix([],Cnt,Cnt).
countTruesInMatrix([R|Rs],SoFar,Cnt):-
    countTruesInRow(R,SoFar,SoFar1),!,
    countTruesInMatrix(Rs,SoFar1,Cnt).
    
countTruesInRow([],SoFar,SoFar).
countTruesInRow([X|Xs],SoFar,Cnt):-
    ((ground(X), X=:=1) ->
        SoFar1 is SoFar + 1,
        countTruesInRow(Xs,SoFar1,Cnt)
    ;
        countTruesInRow(Xs,SoFar,Cnt)).
        
        
% ---------- Print N Queens board ----------
printNQueens(N,Matrix):-
    NK is 2 * N + 1,
    printNQueens_rows(Matrix,NK).

printNQueens_rows([],K):-
    printHR(K).
printNQueens_rows([R|Rs],K):-
    printHR(K),
    printNQueens_row(R),
    printNQueens_rows(Rs,K).

printHR(0):-!,
    writeln('').
printHR(I):-
    write('-'),
    I1 is I - 1,
    printHR(I1).

printNQueens_row([X|Xs]):-!,
    write('|'),
    ((ground(X), X=:=1) -> write('@') ; write('.')),
    printNQueens_row(Xs).
printNQueens_row([]):-!,
    writeln('|').
