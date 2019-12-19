% prob033: Word Design for DNA Computing on Surfaces
% http://www.cse.unsw.edu.au/~tw/csplib/prob/prob033/
% Author: Amit Metodi
% Date: 05/06/2012

:- module('dnaWords', [ dnaWords/2 ]).
:- use_module(dnaVerify).
:- use_module('../auxs/auxMatrix',[matrixCreate/3]).
:- use_module('../auxs/auxRunExpr',[runExpr/5]).

/*

  Usage:
  ------
  ?- Instance=dna(14,8), dnaWords(Instance,Solution),
     auxMatrix:matrixPrint(Solution).

  ?- Instance=dna(15,0), dnaWords(Instance,Solution).

  ?- Instance=dna(0,9), dnaWords(Instance,Solution).

*/

dnaWords(Instance,Solution):-!,
    printInstance(Instance),
    runExpr(Instance,Solution,
            dnaWords:encode,
            dnaWords:decode,
            dnaWords:verify).

printInstance(Instance):-
    writef('%10r,',[Instance]),flush.


verify(_,Words):-
    dnaVerify:verifyDNAWords(Words).


encode(dna(Nt,Nm),(T,M),Cs) :-
    encodeTemplate(Nt,T,Cs-C1),
    encodeMap(Nm,M,C1-[]).

encodeMap(0,[],C-C) :-!.
encodeMap(N,M,CH-CT) :-
    matrixCreate(N,8,M),
    cond_2(M, CH - C1),
    cond_3(M, C1 - C2),
    lexOrder(M, C2 - CT).

encodeTemplate(0,[],C-C) :-!.
encodeTemplate(N,T,CH-CT) :-
    matrixCreate(N,8,T),
    cond_1(T, CH - C1),
    cond_2(T, C1 - C2),
    lexOrder(T, C2 - CT).

% conditoin 1 = Each word in S has 4 symbols from { C,G };
cond_1([X|Xs],[bool_array_sum_eq(X,4)|C1]-C2) :-
    cond_1(Xs, C1-C2).
cond_1([], C-C).
% condition 2 = Each pair of distinct words in S differ in at least 4 positions
cond_2([X|Xs], C1-C3):-
    pairwise(X, Xs, C1-C2),
    cond_2(Xs, C2-C3).
cond_2([], C-C).
% condition 3 = Each pair of words in S, X^R and Y^C differ in at least 4 positions
cond_3([X|Xs], C1-C4) :-
    rev_comp(X, [], XRC),
    pairwise(XRC, [X|Xs], C1-C3),
    cond_3(Xs, C3-C4).
cond_3([], C-C).

pairwise(X,[Y|Ys],C1-C3) :-
    pairwise_xor(X, Y, Z, C1 - [bool_array_sum_geq(Z,4)|C2]),
    pairwise(X, Ys, C2-C3).
pairwise(_,[],C-C).

pairwise_xor([X|Xs], [Y|Ys], [Z|Zs], [bool_xor_reif(X,Y,Z)|C1]-C2):-
    pairwise_xor(Xs, Ys, Zs, C1-C2).
pairwise_xor([], [], [], C-C).

rev_comp([X|Xs],Acc,Ys) :-
    rev_comp(Xs,[-X|Acc],Ys).
rev_comp([],Ys,Ys).

lexOrder([_],Constrs-Constrs).
lexOrder([V1,V2|Vs],[bool_arrays_lexLt(V1,V2)|ConstrsH]-ConstrsT):-
       lexOrder([V2|Vs],ConstrsH-ConstrsT).


decode((T,M), Solution):-
     fixWords(T,M,Solution).

fixWords([T|Templetes],Map,Words):-
     fixWord(Map,T,Words-WordsT),
     fixWords(Templetes,Map,WordsT).
fixWords([],_,[]).

fixWord([M|Ms],T,[W|WordsH]-WordsT):-
     mix2word(T,M,W),
     fixWord(Ms,T,WordsH-WordsT).
fixWord([],_,Words-Words).

mix2word([1|T],[-1|M],['C'|W]):-mix2word(T,M,W).
mix2word([1|T],[1|M],['G'|W]):-mix2word(T,M,W).
mix2word([-1|T],[-1|M],['A'|W]):-mix2word(T,M,W).
mix2word([-1|T],[1|M],['T'|W]):-mix2word(T,M,W).
mix2word([],[],[]).