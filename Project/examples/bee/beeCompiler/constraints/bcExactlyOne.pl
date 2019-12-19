% Author: Amit Metodi
% Last Updated: 05/09/2016

:- module(bcExactlyOne, [ ]).
:- use_module('../auxs/auxLiterals').

%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
exoType([
         bcExactlyOne:exoSimplify,
         skipSimplify,
         0,
         bcExactlyOne:exo2cnf,
         exactlyOne
        ]):-!.

% -------------
% | Simplify  |
% -------------
exoSimplify(Constr,NewConstr,Changed):-!,
    Constr=bc(Type,Vec),
    atMostOne:atMostOneSimplify(Vec,NVec,FoundOne,Changed),
    (ground(FoundOne) -> %(FoundOne==1 ; FoundOne==2) ->
        Changed=1,
        NewConstr=none ;
    (NVec=[A,B] ->
        Changed=1,
        plitUnifyDiff(A,B),
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
    ))))).


:- if(bSettings:exactlyOneEncoding(direct)).

exo2cnf(bc(_Type,Vec),CnfH-CnfT):-!,
    plits2lits(Vec,Xs),!,
    exoDirectCnf(Xs,CnfH-CnfT).

:- elif(bSettings:exactlyOneEncoding(decompose)).

:- if(bSettings:atMostOneEncoding(commander(_))).
:- bSettings:atMostOneEncoding(Option),writef('WARNING: At Most One encoding set to %w !\n         Set bSettings:exactlyOneEncoding to %w to generate a better CNF !\n',[Option,Option]),flush_output.
:- endif.

exo2cnf(bc(_Type,Vec),CnfH-CnfT):-!,
    plits2lits(Vec,Xs),!,
    length(Xs,N),!,
    bcAtMostOne:atMostOne2clauses(Xs,N,CnfH-CnfM),
    bcAtLeastOne:atLeastOne2clauses(Xs,N,CnfM-CnfT).

:- elif(bSettings:exactlyOneEncoding(commander(_))).

:- Head=exo2cnf(bc(_Type,Vec),CnfH-CnfT),
   bSettings:exactlyOneEncoding(commander(K)),!,
   Body=(
       !,
       plits2lits(Vec,Xs),!,
       length(Xs,N),!,
       exoCommanderCnf(Xs,N,K,CnfH-CnfT)
   ),
   dynamic(Head),
   assertz(Head :- Body),
   compile_predicates([Head]).

exoCommanderCnf(Xs,N,K,CnfH-CnfT):-!,
   (N =< K+1 ->
       exoDirectCnf(Xs,CnfH-CnfT) ;
   (N =< 2*K ->
       PartA is ceil(N/2),
       auxLists:listSplit(PartA,Xs,XsA,XsB),
       append(XsA,[T],XsAa),
       append(XsB,[-T],XsBb),!,
       exoDirectCnf(XsAa,CnfH-CnfM),!,
       exoDirectCnf(XsBb,CnfM-CnfT)
   ;
       auxLists:listCalcPartitions(N,K,Parts,0,PartsCnt),
       exoCommanderCnf_(Parts,Xs,Ys,CnfH-CnfM),!,
       exoCommanderCnf(Ys,PartsCnt,K,CnfM-CnfT)
   )).

:- else.
:- bSettings:exactlyOneEncoding(X), writef('ERROR: "%w" is wrong value for bSettings:exactlyOneEncoding !\n',[X]),flush_output,halt.
:- endif.

%% exoCommanderCnf_ also used by bcAtMostOne when using commander
exoCommanderCnf_([_],Xs,[Y],CnfH-CnfT):-!,
    append(Xs,[-Y],XsY),!,
    exoDirectCnf(XsY,CnfH-CnfT).
exoCommanderCnf_([N|Parts],Xs,[Yi|Ys],CnfH-CnfT):-!,
    auxLists:listSplit(N,Xs,XsI,RXs),!,
    append(XsI,[-Yi],XsY),
    exoDirectCnf(XsY,CnfH-CnfM),!,
    exoCommanderCnf_(Parts,RXs,Ys,CnfM-CnfT).


exoDirectCnf(Xs,CnfH-CnfT):-!,
    bcAtMostOne:atMostOneDirectCnf(Xs,CnfH-[Xs|CnfT]).