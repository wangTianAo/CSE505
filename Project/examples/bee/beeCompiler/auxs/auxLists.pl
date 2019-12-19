% Functions on Lists
% Author: Amit Metodi
% Last Updated: 29/01/2016

:- module(auxLists, [ list2diflist/2,
                      listDropFrom/3, listKeepFrom/3,
                      listSplit/4, listOddEvenSplit/3,
                      listListOf/3,
                      listPrint/1
                      ]).


% -------------------------------------
% | List to Different List            |
% -------------------------------------
list2diflist([X|Xs],[X|LH]-LT):-list2diflist(Xs,LH-LT).
list2diflist([],L-L).

% -------------------------------------
% | List dorp/keep/split              |
% -------------------------------------
listDropFrom(0,List,List).
listDropFrom(1,[_|List],List).
listDropFrom(2,[_,_|List],List).
listDropFrom(3,[_,_,_|List],List).
listDropFrom(4,[_,_,_,_|List],List).
listDropFrom(5,[_,_,_,_,_|List],List).
listDropFrom(I,[_,_,_,_,_,_|List],SList):-
    I1 is I - 6,!,
    listDropFrom(I1,List,SList).

listKeepFrom(0,_,[]).
listKeepFrom(1,[X|_],[X]).
listKeepFrom(2,[X1,X2|_],[X1,X2]).
listKeepFrom(3,[X1,X2,X3|_],[X1,X2,X3]).
listKeepFrom(4,[X1,X2,X3,X4|_],[X1,X2,X3,X4]).
listKeepFrom(5,[X1,X2,X3,X4,X5|_],[X1,X2,X3,X4,X5]).
listKeepFrom(I,[X1,X2,X3,X4,X5,X6|Xs],[X1,X2,X3,X4,X5,X6|KXs]):-
    I6 is I - 6,!,
    listKeepFrom(I6,Xs,KXs).

listSplit(0,L,[],L).
listSplit(1,[X|L],[X],L).
listSplit(2,[X1,X2|L],[X1,X2],L).
listSplit(3,[X1,X2,X3|L],[X1,X2,X3],L).
listSplit(4,[X1,X2,X3,X4|L],[X1,X2,X3,X4],L).
listSplit(5,[X1,X2,X3,X4,X5|L],[X1,X2,X3,X4,X5],L).
listSplit(I,[X1,X2,X3,X4,X5,X6|RL],[X1,X2,X3,X4,X5,X6|NL],L):-
    I6 is I - 6,!,
    listSplit(I6,RL,NL,L).
    
    
% -------------------------------
% | Split Odd Even              |
% -------------------------------
% split L=[a0,a1,a2,a3...] to two lists L1=[a0, a2...] and L1=[a1, a3...]
listOddEvenSplit([A,B|Xs],[A|As],[B|Bs]):-
       listOddEvenSplit(Xs,As,Bs).
listOddEvenSplit([A],[A],[]).
listOddEvenSplit([],[],[]).



% -------------------------------
% | Create List of 'X's         |
% -------------------------------
listListOf(0,_,[]).
listListOf(1,X,[X]).
listListOf(2,X,[X,X]).
listListOf(3,X,[X,X,X]).
listListOf(4,X,[X,X,X,X]).
listListOf(I,X,[X,X,X,X,X|Xs]):-
    I1 is I - 5,
    listListOf(I1,X,Xs).


% -------------------------------------
% | Calculate list partitioning  sizes|
% -------------------------------------
%listCalcPartitions(+N,+K,-Parts,+CurCnt,-PartsCnt)
% N - list size
% K - max partition size
% Parts - the size of the partitions
% CurCnt - current partition count (should be 0 in first call)
% PartsCnt - Amount of partitions in Parts

listCalcPartitions(0,_,[],Cnt,Cnt):-!.
listCalcPartitions(N,K,[N],I,Cnt):-
   N =< K, !,
   Cnt is I + 1.
listCalcPartitions(N,K,[PartSize|Ss],I,Cnt):-
   Parts is ceil(N/K),
   PartSize is ceil(N / Parts),
   NN is N - PartSize,
   I1 is I + 1,
   listCalcPartitions(NN,K,Ss,I1,Cnt).


% -------------------------------
% | List Print                  |
% -------------------------------
listPrint([X|Xs]):-writeln(X),!,listPrint(Xs).
listPrint([]):-!.