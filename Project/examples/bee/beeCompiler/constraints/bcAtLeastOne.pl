% Author: Amit Metodi
% Last Updated: 29/01/2016

:- module(bcAtLeastOne, [ ]).
:- use_module('../auxs/auxLiterals').
%:- use_module('../auxs/atLeastOne').

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=bool_array_or(Bs,ConstrsH-ConstrsT),
   Body=(
       !,
       bcAtLeastOne:aloType(Type),
       auxLiterals:lits2plits(Bs,Vec),
       bcAtLeastOne:aloSimplify(bc(Type,Vec),Constr,_),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).


%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
aloType([
         bcAtLeastOne:aloSimplify,
         skipSimplify,
         0,
         bcAtLeastOne:alo2cnf,
         atLeastOne
        ]):-!.

aloSimplify(Constr,NewConstr,Changed):-!,
    Constr=bc(Type,Vec),
    atLeastOne:atLeastOneSimplify(Vec,NVec,FoundOne,Changed),
    (FoundOne==1 ->
        Changed=1,
        NewConstr=none ;
    (NVec=[PBit] ->
        Changed=1,
        plitAsgnTrue(PBit),
        NewConstr=none ;
    (NVec=[] ->
        throw(unsat) ;
    (Changed==1 ->
        NewConstr=bc(Type,NVec)
    ;
        NewConstr=Constr
    )))).
    
    
alo2cnf(bc(_Type,Vec),CnfH-CnfT):-!,
    plits2lits(Vec,Xs),!,
    length(Xs,N),!,
    atLeastOne2clauses(Xs,N,CnfH-CnfT).

atLeastOne2clauses(Xs,N,CnfH-CnfT):-!,
      (N =< 8 ->
           CnfH=[Xs|CnfT] ;
      (N =< 14 ->
           N1 is N - (N // 2),
           auxLists:listSplit(N1,Xs,Xs1,Xs2),
           append(Xs1,[Z],ZXs1),
           append(Xs2,[-Z],ZXs2),
           CnfH=[ZXs1,ZXs2|CnfT] ;
      % commander
      auxLists:listCalcPartitions(N,7,Parts,0,N2),!,
      atLeastOne2clauses(Parts,Xs,TXs,CnfH-CnfM),!,
      atLeastOne2clauses(TXs,N2,CnfM-CnfT)
      )).

atLeastOne2clauses([Size|Parts],Xs,[Z|TXs],[ZXs1|CnfH]-CnfT):-!,
      auxLists:listSplit(Size,Xs,Xs1,Xs2),!,
      append(Xs1,[-Z],ZXs1),
      atLeastOne2clauses(Parts,Xs2,TXs,CnfH-CnfT).
atLeastOne2clauses([],[],[],Cnf-Cnf):-!.