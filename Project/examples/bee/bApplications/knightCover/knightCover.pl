% KNIGHT COVERINGS PROBLEM
% Author: Amit Metodi
% Last Update: 05/06/2012

:- module('knightCover', [
                knightCover/2,
                printKnigts/2
                ]).

:- use_module('../auxs/auxMatrix',[matrixCreate/3, matrixGetCell0/4]).
:- use_module('../auxs/auxRunExpr',[runExprMin/5]).

/*
   USAGE:
   ------
   ?- Instance=6, knightCover(Instance,Solution), printKnigts(Instance,Solution).

*/

knightCover(Instance,Solution):-!,
    printInstance(Instance),
    runExprMin(Instance,Solution,
            knightCover:encode,
            knightCover:decode,
            knightCover:verify).


printInstance(Instance):-
    writef('%5r,',[Instance]),flush.


%%% ENCODE

boundKnights(N,Lower,Upper):-
    Lower is ceil(N*N/9),
    %% (4x6) board can be fill with 4 knights
    Rows4 is ceil(N / 4),
    Cols6 is ceil(N / 6),
    Upper is Rows4*Cols6*4.

encode(N,Ks,SumKs,Constraints):-
     matrixCreate(N,N,Ks),
     cellConstraints(0,0,N,Ks,Constraints-ConstraintsM),
     boundKnights(N,Lower,Upper),
     append(Ks,FlatKs),
     ConstraintsM=[new_int(SumKs,Lower,Upper),bool_array_sum_eq(FlatKs,SumKs)].

cellConstraints(_,N,N,_,Constraints-Constraints):-!.
cellConstraints(N,J,N,Ks,ConstraintsH-ConstraintsT):-!,
   J1 is J + 1,
   cellConstraints(0,J1,N,Ks,ConstraintsH-ConstraintsT).
cellConstraints(I,J,N,Ks,ConstraintsH-ConstraintsT):-!,
   matrixGetCell0(Ks,I,J,Kij),
   Im1 is I - 1,
   Ip1 is I + 1,
   Im2 is I - 2,
   Ip2 is I + 2,
   Jm2 is J - 2,
   Jp2 is J + 2,
   Jm1 is J - 1,
   Jp1 is J + 1,
   (matrixGetCell0(Ks,Im2,Jm1,Km2m1) ; Km2m1= -1),
   (matrixGetCell0(Ks,Ip2,Jm1,Kp2m1) ; Kp2m1= -1),
   (matrixGetCell0(Ks,Im2,Jp1,Km2p1) ; Km2p1= -1),
   (matrixGetCell0(Ks,Ip2,Jp1,Kp2p1) ; Kp2p1= -1),

   (matrixGetCell0(Ks,Im1,Jm2,Km1m2) ; Km1m2= -1),
   (matrixGetCell0(Ks,Ip1,Jm2,Kp1m2) ; Kp1m2= -1),
   (matrixGetCell0(Ks,Im1,Jp2,Km1p2) ; Km1p2= -1),
   (matrixGetCell0(Ks,Ip1,Jp2,Kp1p2) ; Kp1p2= -1),
   ConstraintsH=[
                 % A<-> cell is attacked by knight
                 bool_array_or_reif([Km2m1,Kp2m1,Km2p1,Kp2p1,Km1m2,Kp1m2,Km1p2,Kp1p2],Attacked),
                 % cell attacked by knight or knight
                 bool_array_or([Kij,Attacked])
                 |ConstraintsM],
   cellConstraints(Ip1,J,N,Ks,ConstraintsM-ConstraintsT).

%%% DECODE

decode(Matrix,Matrix).


%%% VERIFY

verify(N,Board):-
     matrixCreate(N,N,As),!,
     verify(0,0,N,Board,As),!,
     ground(As).

verify(_,N,N,_,_):-!.
verify(N,J,N,Ks,As):-!,
   J1 is J + 1,
   verify(0,J1,N,Ks,As).
verify(I,J,N,Ks,As):-!,
   matrixGetCell0(Ks,I,J,Kij),
   Ip1 is I + 1,
   (Kij=:=1 ->
       Im1 is I - 1,
       Im2 is I - 2,
       Ip2 is I + 2,
       Jm2 is J - 2,
       Jp2 is J + 2,
       Jm1 is J - 1,
       Jp1 is J + 1,
       matrixGetCell0(As,I,J,1),
       (matrixGetCell0(As,Im2,Jm1,1) ; true),
       (matrixGetCell0(As,Ip2,Jm1,1) ; true),
       (matrixGetCell0(As,Im2,Jp1,1) ; true),
       (matrixGetCell0(As,Ip2,Jp1,1) ; true),
       (matrixGetCell0(As,Im1,Jm2,1) ; true),
       (matrixGetCell0(As,Ip1,Jm2,1) ; true),
       (matrixGetCell0(As,Im1,Jp2,1) ; true),
       (matrixGetCell0(As,Ip1,Jp2,1) ; true)
   ;
       true
   ),!,
   verify(Ip1,J,N,Ks,As).
   
   
   
% ---------- Print N Queens board ----------
printKnigts(N,Matrix):-
    NK is 2 * N + 1,
    printKnigts_rows(Matrix,NK).

printKnigts_rows([],K):-
    printHR(K).
printKnigts_rows([R|Rs],K):-
    printHR(K),
    printKnigts_row(R),
    printKnigts_rows(Rs,K).

printHR(0):-!,
    writeln('').
printHR(I):-
    write('-'),
    I1 is I - 1,
    printHR(I1).

printKnigts_row([X|Xs]):-!,
    write('|'),
    ((ground(X), X=:=1) -> write('@') ; write('.')),
    printKnigts_row(Xs).
printKnigts_row([]):-!,
    writeln('|').