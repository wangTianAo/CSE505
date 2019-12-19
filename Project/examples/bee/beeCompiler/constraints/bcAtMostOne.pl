% Author: Amit Metodi
% Last Updated: 05/09/2016

:- module(bcAtMostOne, [ ]).
:- use_module('../auxs/auxLiterals').
%:- use_module('../auxs/atMostOne').
%:- use_module('../auxs/weightBits').  % For 'sumbits' decomposition

:- if(bSettings:atMostOneEncoding(sumbits)).
amoType([
         bcAtMostOne:amoSimplify,
         skipSimplify,
         bcAtMostOne:amoDecompose,
         0,
         atMostOne
        ]):-!.
:- else.
amoType([
         bcAtMostOne:amoSimplify,
         skipSimplify,
         0,
         bcAtMostOne:amo2cnf,
         atMostOne
        ]):-!.
:- endif.

amoSimplify(Constr,NewConstr,Changed):-!,
    Constr=bc(Type,Vec),
    atMostOne:atMostOneSimplify(Vec,NVec,FoundOne,Changed),
    ((ground(FoundOne) ; NVec=[] ; NVec=[_]) -> % FoundOne==(1 or 2)
        Changed=1,
        NewConstr=none ;
    (Changed==1 ->
        NewConstr=bc(Type,NVec)
    ;
        NewConstr=Constr
    )).
    
    
:- if(bSettings:atMostOneEncoding(product(_))).

%%% ----- Product Encoding for At Most One ----- %%%

amo2cnf(bc(_Type,Vec),CnfH-CnfT):-!,
    plits2lits(Vec,Xs),!,
    length(Xs,N),!,
    atMostOne2clauses(Xs,N,CnfH-CnfT).

:- Head=atMostOne2clauses(Xs,XsLen,CnfH-CnfT),
   bSettings:atMostOneEncoding(product(K)),!,
   Body=(
       !,
       (XsLen < K ->
           atMostOneDirectCnf(Xs,CnfH-CnfT)
       ;
           calculateDs(XsLen,Ulen,Vlen),
           length(U,Ulen),
           atMostOne2clauses(U,Ulen,CnfH-CnfM1),
           length(V,Vlen),!,
           atMostOne2clauses(V,Vlen,CnfM1-CnfM2),!,
           atMostOne2clauses_d1(U,Xs,U,CnfM2-CnfM3),!,
           atMostOne2clauses_d2(V,Xs,Ulen,CnfM3-CnfT)
       )
   ),
   dynamic(Head),
   assertz(Head :- Body),
   compile_predicates([Head]).

calculateDs(N,D1,D2):-
    D1 is ceil(sqrt(N)),
    D2 is ceil(N / D1).

atMostOne2clauses_d1([Ui|Us],[Xij|Xs],OrgUs,[[-Xij,Ui]|CnfH]-CnfT):-!,
    atMostOne2clauses_d1(Us,Xs,OrgUs,CnfH-CnfT).
atMostOne2clauses_d1(_,[],_,Cnf-Cnf):-!.
atMostOne2clauses_d1([],Xs,Us,CnfH-CnfT):-!,
    atMostOne2clauses_d1(Us,Xs,Us,CnfH-CnfT).

atMostOne2clauses_d2([Vi],Xs,_,CnfH-CnfT):-!,
    xiDragY(Xs,Vi,CnfH-CnfT).
atMostOne2clauses_d2([Vi|Vs],Xs,ULen,CnfH-CnfT):-!,
    auxLists:listSplit(ULen,Xs,XsVi,RXs),
    xiDragY(XsVi,Vi,CnfH-CnfM),!,
    atMostOne2clauses_d2(Vs,RXs,ULen,CnfM-CnfT).

:- elif(bSettings:atMostOneEncoding(commander(_))).

amo2cnf(bc(_Type,Vec),CnfH-CnfT):-!,
    plits2lits(Vec,Xs),!,
    length(Xs,N),
    amoCommanderCnf(Xs,N,CnfH-CnfT).

:- Head=amoCommanderCnf(Xs,N,CnfH-CnfT),
   bSettings:atMostOneEncoding(commander(K)),!,
   Body=(
       !,
       (N =< K+1 ->
           atMostOneDirectCnf(Xs,CnfH-CnfT)
       ;
           auxLists:listCalcPartitions(N,K,Parts,0,PartsCnt),
           bcExactlyOne:exoCommanderCnf_(Parts,Xs,Ys,CnfH-CnfM),!,
           amoCommanderCnf(Ys,PartsCnt,CnfM-CnfT)
       )
   ),
   dynamic(Head),
   assertz(Head :- Body),
   compile_predicates([Head]).

:- elif(bSettings:atMostOneEncoding(pairwise)).

%%% ----- Standard Encoding for At Most One ----- %%%

amo2cnf(bc(_Type,Vec),CnfH-CnfT):-!,
    plits2lits(Vec,Xs),!,
    atMostOneDirectCnf(Xs,CnfH-CnfT).

atMostOne2clauses(Xs,_XsLen,CnfH-CnfT):-!,
    atMostOneDirectCnf(Xs,CnfH-CnfT).

:- elif(bSettings:atMostOneEncoding(sumbits)).

amoDecompose(bc(_TypeAMO,Vec),Constrs):-!,
    weightBits:plits2wbits(Vec,WBits),!,
    bcSumBitsLEqK:sumBitsLEqKDecompose(bc(_Type,[1|WBits]),Constrs).

:- elif(bSettings:atMostOneEncoding(clause)).

%%% ----- Standard Encoding for At Most One ----- %%%

amo2cnf(bc(_Type,Vec),CnfH-CnfT):-!,
    plits2lits(Vec,Xs),!,
    atMostOne2clauses(Xs,_XsLen,CnfH-CnfT).

atMostOne2clauses(Xs,_XsLen,[[amo|Xs]|Cnf]-Cnf):-!.

:- else.
:- bSettings:atMostOneEncoding(X), writef('ERROR: "%w" is wrong value for bSettings:atMostOneEncoding !\n',[X]),flush_output,halt.
:- endif.


atMostOneDirectCnf([_],Cnf-Cnf):-!.
atMostOneDirectCnf([X|Xs],CnfH-CnfT):-!,
        xiDragY(Xs,-X,CnfH-CnfM),
        atMostOneDirectCnf(Xs,CnfM-CnfT).

xiDragY([Xi|Xs],Y,[[Y,-Xi]|CnfH]-CnfT):-!,
    xiDragY(Xs,Y,CnfH-CnfT).
xiDragY([],_,Cnf-Cnf):-!.