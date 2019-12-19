% Author: Amit Metodi
% Last Updated: 05/03/2012

:- module(bcOr, [ ]).
:- use_module('../auxs/auxLiterals').
%:- use_module('../auxs/atLeastOne').

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=bool_array_or_reif(Bs,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcOr:orType(OrType),
       auxLiterals:lits2plits(Bs,OrVec),
       bcOr:orSimplify(bc(OrType,[Z|OrVec]),Constr,_),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_array_and_reif(Bs,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcOr:orType(OrType),
       auxLiterals:litNotXs(Bs,NBs),
       auxLiterals:lits2plits(NBs,OrVec),
       bcOr:orSimplify(bc(OrType,[-Z|OrVec]),Constr,_),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_or_reif(A,B,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcOr:orType(OrType),
       auxLiterals:lits2plits([A,B],OrVec),
       bcOr:orSimplify(bc(OrType,[Z|OrVec]),Constr,_),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_and_reif(A,B,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcOr:orType(OrType),
       auxLiterals:lits2plits([-A,-B],OrVec),
       bcOr:orSimplify(bc(OrType,[-Z|OrVec]),Constr,_),
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
orType([
        bcOr:orSimplify,
        bcOr:orSimplifyAdv,
        0,
        bcOr:or2cnf,
        or
       ]):-!.

%%% [Z|OrVec] Z=literal , OrVec=[PureLit,...,PureLit]
orSimplify(Constr,NewConstr,Changed):-!,
    Constr=bc(Type,[Z|OrVec]),
    (ground(Z) ->
        Changed=1,
        (Z =:= 1 ->
           bcAtLeastOne:aloType(ALOType),
           bcAtLeastOne:aloSimplify(bc(ALOType,OrVec),NewConstr,_)
        ;
           plitAsgnFalses(OrVec),
           NewConstr=none
        ) ;
    atLeastOne:atLeastOneSimplify(OrVec,NOrVec,FoundOne,Changed),
    (FoundOne==1 ->
        Changed=1,
        litAsgnTrue(Z),
        NewConstr=none ;
    (NOrVec=[] ->
        Changed=1,
        litAsgnFalse(Z),
        NewConstr=none ;
    (NOrVec=[PBit] ->
        Changed=1,
        lit2plit(Z,Zl,Zop),
        plitUnify((Zl,Zop),PBit),
        NewConstr=none ;
    (Changed==1 ->
        NewConstr=bc(Type,[Z|NOrVec])
    ;
        NewConstr=Constr
    ))))).

orSimplifyAdv(Constr,NewConstr,Changed):-!,
    Constr=bc(_Type,[Z|OrVec]),
    lit2plit(Z,Zl,Zop),
    isContainsVar(OrVec,Zl,FoundOp),
    (ground(FoundOp) ->
        (Zop=:=FoundOp ->
            (OrVec = [X1,X2] ->
                Changed=1,
                X1 = (X1l,X1op),
                X2 = (X2l,X2op),
                (X1l == Zl ->
                    X2opNeg is -X2op,
                    NewOrVec=[(Zl,Zop), (X2l,X2opNeg)]
                ;
                    X1opNeg is -X1op,
                    NewOrVec=[(Zl,Zop), (X1l,X1opNeg)]
                ),
                bcAtLeastOne:aloType(ALOType),
                bcAtLeastOne:aloSimplify(bc(ALOType,NewOrVec),NewConstr,_)
            ;
                NewConstr=Constr
            )
        ;
            Changed=1,
            litAsgnTrue(Z),
            bcAtLeastOne:aloType(ALOType),
            bcAtLeastOne:aloSimplify(bc(ALOType,OrVec),NewConstr,_)
        )
    ;
        NewConstr=Constr
    ).

isContainsVar([],_,_):-!.
isContainsVar([(Xl,Xop)|OrVec],Zl,FoundOp):-!,
    (Xl == Zl ->
        FoundOp=Xop
    ;
        isContainsVar(OrVec,Zl,FoundOp)
    ).

or2cnf(bc(_,[Z|OrVec]),CnfH-CnfT):-!,
     plitXiDragY(OrVec,Z,CnfH-CnfM),!,
     plits2lits(OrVec,Xs),!,
     length([-Z|Xs],N),!,
     bcAtLeastOne:atLeastOne2clauses([-Z|Xs],N,CnfM-CnfT).


% Xi -> Y
plitXiDragY([(Zl,Zop)|Xs],Y,[[Z, Y]|CnfH]-CnfT):-!,
    (Zop =:= 1 -> Z= -Zl ; Z= Zl),!,
    plitXiDragY(Xs,Y,CnfH-CnfT).
plitXiDragY([],_,Cnf-Cnf):-!.
