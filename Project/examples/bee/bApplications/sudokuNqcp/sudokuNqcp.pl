% solving Sudoku / QCP
% Author: Amit Metodi
% Last Updated: 05/06/2012

:- module('sudokuNqcp', [solveSudoku/2,
                         solveQCP/2 ]).

:- use_module('../auxs/auxMatrix',[matrixCreate/3, matrixTranspose/2, matrixGetCell/4, matrixGetSubMtrx0/6, matrix2vector/2]).
:- use_module('../auxs/auxRunExpr',[runExpr/5, decodeInt/2, decodeIntMatrix/2]).

/*
  INSTANCE FORMAT:
  ----------------
  QCP: qcp(N,Inputs)
  Where: N is the height/width of the board
         Inputs is a list tuples (X,Y,Val)

  Sudoku: sudoku(Sw,Sh,Inputs)
  Where: Sw is square width, Sh is square height (N is Sw*Sh)
         Inputs is a list tuples (X,Y,Val)

  USAGE:
  ------
  ?- Instance=sudoku(3,3,[(1,1,1)]),
     solveSudoku(Instance, Solution),
     auxMatrix:matrixPrint(Solution).
*/

solveSudoku(Instance, Solution) :-
    runExpr(Instance,Solution,
            sudokuNqcp:encodeSudoku,
            sudokuNqcp:decode,
            sudokuNqcp:verifySudoku).

solveQCP(Instance, Solution) :-
    runExpr(Instance,Solution,
            sudokuNqcp:encodeQCP,
            sudokuNqcp:decode,
            sudokuNqcp:verifyQCP).


encodeSudoku(sudoku(Sw,Sh,Inputs), Map, Constraints):-
    N is Sw*Sh,
    matrixCreate(N,N,Map),
    assignInputs(Inputs,Map),
    newNumbersInMatrix(Map,1,N,Constraints-C1),
    allDiffRows(Map,C1-C2),
    matrixTranspose(Map,MapTr),
    allDiffRows(MapTr,C2-C3),
    getSqrsAsLists(Sh,Sw,Sh,Sw,Map,Vecs),
    allDiffRows(Vecs,C3-[]).

encodeQCP(qcp(N,Inputs), Map, Constraints):-
    matrixCreate(N,N,Map),
    assignInputs(Inputs,Map),
    newNumbersInMatrix(Map,1,N,Constraints-C1),
    allDiffRows(Map,C1-C2),
    matrixTranspose(Map,MapTr),
    allDiffRows(MapTr,C2-[]).

decode(Map, Solution):-
    decodeIntMatrix(Map,Solution).


% ----- Encode Aux ----- %
assignInputs([(X,Y,V)|Inputs],Map):-
    matrixGetCell(Map,X,Y,V),
    assignInputs(Inputs,Map).
assignInputs([],_).

newNumbersInMatrix([R|Rs],Min,Max,C1-C3):-
    newNumbersInMatrix_Row(R,Min,Max,C1-C2),
    newNumbersInMatrix(Rs,Min,Max,C2-C3).
newNumbersInMatrix([],_,_,C-C).

newNumbersInMatrix_Row([X|Xs],Min,Max,[new_int(X,Min,Max)|C1]-C2):-
    var(X),!,
    newNumbersInMatrix_Row(Xs,Min,Max,C1-C2).
newNumbersInMatrix_Row([_|Xs],Min,Max,C1-C2):-!,
    newNumbersInMatrix_Row(Xs,Min,Max,C1-C2).
newNumbersInMatrix_Row([],_,_,C-C).

allDiffRows([Row|Rows],[int_array_allDiff(Row)|C1]-C2):-
   allDiffRows(Rows,C1-C2).
allDiffRows([],C-C).

     
% ----- Sudoku Aux ----- %

getSqrsAsLists(_,0,_,_,_,[]):-!.
getSqrsAsLists(0,Sy,Sh,Sw,Board,Vecs):-!,
     Sy1 is Sy - 1,
     getSqrsAsLists(Sh,Sy1,Sh,Sw,Board,Vecs).
getSqrsAsLists(Sx,Sy,Sh,Sw,Board,[Vec|Vecs]):-
     StartX is (Sx - 1) * Sw,
     StartY is (Sy - 1) * Sh,
     matrixGetSubMtrx0(Board,StartX,StartY,Sw,Sh,SubMtrx),!,
     matrix2vector(SubMtrx,Vec),!,
     Sx1 is Sx - 1,
     getSqrsAsLists(Sx1,Sy,Sh,Sw,Board,Vecs).
     
% ----- Verify solutions ------ %

verifyQCP(qcp(N,Inputs),Solution):-
    assignInputs(Inputs,Solution),!,
    permutationInRows(Solution,1,N),!,
    matrixTranspose(Solution,SolutionTr),!,
    permutationInRows(SolutionTr,1,N).

verifySudoku(sudoku(Sw,Sh,Inputs),Solution):-
    N is Sw * Sh,
    assignInputs(Inputs,Solution),!,
    permutationInRows(Solution,1,N),!,
    matrixTranspose(Solution,SolutionTr),!,
    permutationInRows(SolutionTr,1,N),!,
    getSqrsAsLists(Sh,Sw,Sh,Sw,Solution,Vecs),!,
    permutationInRows(Vecs,1,N).

permutationInRows([Ints|Rows],Start,End):-
    sort(Ints,SInts),
    !,permutationInRow(SInts,Start,End),
    !,permutationInRows(Rows,Start,End).
permutationInRows([],_,_).

permutationInRow([Val],Val,Val):-!.
permutationInRow([Start|Vals],Start,End):-!,
    Next is Start + 1,
    permutationInRow(Vals,Next,End).
