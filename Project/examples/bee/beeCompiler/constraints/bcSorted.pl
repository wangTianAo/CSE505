% Components: Sorted
% Author: Amit Metodi
% Last Updated: 01/07/2012

:- module(bcSorted, []).
:- use_module('../auxs/auxLiterals').

sortedType([
            bcSorted:sortedSimplify,
            skipSimplify,
            0,
            bcSorted:sorted2cnf,
            sorted
           ]).

% -------------------------------
% | Reduce Sorted               |
% -------------------------------
sortedSimplify(Constr,NewConstr, Changed):-!,
    Constr=bc(Type,Xs),
    simplifySorted(Xs, NXs, Changed),
    ((NXs=[] ; NXs=[_]) ->
        NewConstr=none ;
    (Changed==1 ->
        NewConstr=bc(Type,NXs)
    ;
        NewConstr=Constr
    )).


simplifySorted(Xs,NXs,Changed):-!,
    simplifySorted_s(Xs,TXs,Changed),!,
    (Changed==1 ->
        ((TXs=[X0|_], ground(X0)) ->
            removeLeadingOnes(TXs,NXs)
        ;
            NXs=TXs
        )
    ;
        NXs=Xs
    ).

simplifySorted_s([X|Xs],NXs,Changed):-!,
    (ground(X) ->
        Changed=1,
        (X =:= 1 ->
            simplifySorted_s(Xs,NXs,Changed)
        ;
            NXs=[],
            litAsgnFalses(Xs)
        )
    ;
        NXs=[X|MXs],
        lit2plit(X,Xl,Xop),
        simplifySorted_m(Xs,[(Xl,Xop)],MXs,Changed)
    ).
simplifySorted_s([],[],_):-!.

simplifySorted_m([X|Xs],RNXs,NXs,Changed):-!,
    (ground(X) ->
        Changed=1,
        (X =:= -1 ->
            NXs=[],
            litAsgnFalses(Xs)
        ;
            plitAsgnTrues(RNXs),
            simplifySorted_s(Xs,NXs,_)
        )
    ;
    RNXs=[(PXl,PXop)|_],
    lit2plit(X,Xl,Xop),
    (Xl==PXl ->
        Changed=1,
        (Xop==PXop ->
            simplifySorted_m(Xs,RNXs,NXs,Changed)
        ;
            plitAsgnTrues(RNXs),
            litAsgnFalses(Xs),
            NXs=[]
        )
    ;
        NXs=[X|MXs],
        simplifySorted_m(Xs,[(Xl,Xop)|RNXs],MXs,Changed)
    )).
simplifySorted_m([],_,[],_):-!.

removeLeadingOnes([X|Xs],NXs):-!,
    (ground(X) ->
        (X=:=1 ->
            removeLeadingOnes(Xs,NXs)
        ;
            %throw(bug(simplify,sorted))
            fail
        )
    ;
        NXs=[X|Xs]
    ).
removeLeadingOnes([],[]):-!.


% -------------------------------
% | Encode Sorted               |
% -------------------------------
% Ai+1->Ai
sorted2cnf(bc(_,Xs),CnfH-CnfT):-!,
     sortedCnf(Xs,CnfH-CnfT).

sortedCnf([X1,X2|Xs],CnfH-CnfT):-!,
    sortedCnf([X2|Xs],CnfH-[[-X2,X1]|CnfT]).
sortedCnf([_],Cnf-Cnf):-!.
sortedCnf([],Cnf-Cnf):-!.
