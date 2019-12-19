% prob019: magic squares
% http://www.cs.st-andrews.ac.uk/~ianm/CSPLib/prob/prob019/index.html
% Author: Amit Metodi
% Date: 05/06/2012

:- module('magicSquare', [ magicSquare/2 ]).

:- use_module('../auxs/auxRunExpr',[runExpr/5, decodeIntMatrix/2]).
:- use_module('../auxs/auxMatrix',[matrixCreate/3, matrixTranspose/2, matrix2vector/2]).

/*
  Usage:
  ------
  ?- Instance=5, magicSquare(Instance,Solution),
     auxMatrix:matrixPrint(Solution).

*/

magicSquare(Instance,Solution):-!,
    printInstance(Instance),
    garbage_collect,!,
    runExpr(Instance,Solution,
            magicSquare:encode,
            magicSquare:decode,
            magicSquare:verify).

printInstance(Instance):-
    writef('%5r,',[Instance]),flush.

%%% ENCODE

encode(N, Map, Constraints):-
    matrixCreate(N,N,Map),
    NN is N * N ,
    newNumbersInMatrix(Map,1,NN,Constraints-C1),
    matrix2vector(Map,Nums),
    C1=[int_array_allDiff(Nums)|C2],
    MagicSum is N * (N * N + 1)/2,
    magicSum_rows(Map,MagicSum,C2-C3),
    matrixTranspose(Map,MapTr),
    magicSum_rows(MapTr,MagicSum,C3-C4),
    magicSymatricBreak(Map,C4-[]).

newNumbersInMatrix([R|Rs],Min,Max,C1-C3):-
    newNumbersInMatrix_Row(R,Min,Max,C1-C2),
    newNumbersInMatrix(Rs,Min,Max,C2-C3).
newNumbersInMatrix([],_,_,C-C).

newNumbersInMatrix_Row([X|Xs],Min,Max,[new_int(X,Min,Max)|C1]-C2):-
    newNumbersInMatrix_Row(Xs,Min,Max,C1-C2).
newNumbersInMatrix_Row([],_,_,C-C).

magicSum_rows([R|NNSquare],MagicSum,[int_array_plus(R,MagicSum)|C1]-C2):-
    magicSum_rows(NNSquare,MagicSum,C1-C2).
magicSum_rows([],_,C-C).

magicSymatricBreak(NNSquare,CH-CT):-
    NNSquare=[[Cell11,Cell21|Row1]|_],
    CH=[int_eq(Cell11,1)|C1],
    createAgtBcomps([Cell11,Cell21|Row1],C1-C2),
    matrixTranspose(NNSquare,NNSquareTr),
    NNSquareTr=[[Cell11,Cell12|Col1]|_],
    createAgtBcomps([Cell11,Cell12|Col1],C2-C3),
    C3=[int_lt(Cell21,Cell12)|CT].

createAgtBcomps([A,B|Xs],[int_lt(A,B)|C1]-C2):-
    createAgtBcomps([B|Xs],C1-C2).
createAgtBcomps([_],C-C).

%%% DECODE

decode(Map, Solution):-
    decodeIntMatrix(Map,Solution).

%%% VERIFY

verify(N,Solution):-
    NN is N*N,
    MagicSum is N * (NN + 1)/2,
    append(Solution,Ints),!,
    allNumsInRange(Ints,1,NN),!,
    sumRowsEqK(Solution,MagicSum),
    matrixTranspose(Solution,SolutionTr),!,
    sumRowsEqK(SolutionTr,MagicSum).

allNumsInRange(Ints,Start,End):-
    sort(Ints,SInts),
    allNumsInRange_(SInts,Start,End).
    
allNumsInRange_([Val],Val,Val):-!.
allNumsInRange_([Start|Vals],Start,End):-!,
    Next is Start + 1,
    allNumsInRange_(Vals,Next,End).

sumRowsEqK([Row|Rows],MagicSum):-!,
    sumRowsEqK_(Row,MagicSum),!,
    sumRowsEqK(Rows,MagicSum).
sumRowsEqK([],_).

sumRowsEqK_([Val|Vals],Sum):-
    Sum1 is Sum - Val,
    sumRowsEqK_(Vals,Sum1).
sumRowsEqK_([],0).