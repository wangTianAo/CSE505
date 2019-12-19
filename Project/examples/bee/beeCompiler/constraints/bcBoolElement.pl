% Author: Amit Metodi
% Last Updated: 31/05/2017

:- module(bcBoolElement, [ ]).
:- use_module('../auxs/auxLiterals').

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=bool_array_element(Indx,Vec,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcBoolElement:boolElementType(Type),
       bcInteger:getDirectNumber(Indx,(Min,_Max,IBits,_)),
       (Min==0 ->
           bcBoolElement:boolElementSimplify(bc(Type,[IBits,Vec,Z]),Constr,1)
       ;
       (Min < 0 ->
           Xdrop is abs(Min),
           (auxLists:listSplit(Xdrop,IBits,NoIndx,RIBits) ->
               auxLiterals:litAsgnFalses(NoIndx),
               bcBoolElement:boolElementSimplify(bc(Type,[RIBits,Vec,Z]),Constr,1)
           ;
               throw(unsat)
           )
       ;
       % Min > 0
       (auxLists:listDropFrom(Min,Vec,RVec)->
           bcBoolElement:boolElementSimplify(bc(Type,[IBits,RVec,Z]),Constr,1)
       ;
           throw(unsat)
       ))),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).



:- Head=bool_arrays_elements(Indx,Matrix,Vector,ConstrsH-ConstrsT),
   Body=(!,bcBoolElement:decomposeBoolArraysElements(Indx,Matrix,Vector,ConstrsH-ConstrsT)),
   bParser:addConstraint(Head,Body).



%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
boolElementType([
                   bcBoolElement:boolElementSimplify,
                   bcBoolElement:boolElementSimplifyAdv,
                   bcBoolElement:boolElementDecompose,
                   bcBoolElement:boolElement2cnf,
                   boolElement]).

% --------------------------
% | Simplify               |
% --------------------------
boolElementSimplify(Constr,NewConstr,Changed):-
    Constr=bc(Type,[Indx,Bits,Z]),
    (ground(Z) ->
        removeIndxs_ground(Indx,Bits,Z,NIndx,NBits,Changed)
    ;
        removeIndxs_simple(Indx,Bits,NIndx,NBits,Changed)
    ),
    (Changed==1 ->
        (NIndx=[] -> throw(unsat) ;
        (NIndx=[I0] ->
            litAsgnTrue(I0),
            NBits=[B0],
            litUnify(B0,Z),
            NewConstr=none ;
        (NIndx=[I0,I1] ->
            litUnify(I0,-I1),
            NBits=[B0,B1],
            bcITE:iteReifType(ITEType),
            bcITE:iteReifSimplify(bc(ITEType,[I0,B0,B1,Z]),NewConstr,_) ;
        NewConstr=bc(Type,[NIndx,NBits,Z])
        )))
    ;
        NewConstr=Constr
    ).


removeIndxs_simple([I|Is],[B|Bs],NIs,NBs,Changed):-
    (ground(I) ->
        Changed=1,
        (I=:= -1 ->
            removeIndxs_simple(Is,Bs,NIs,NBs,_)
        ;
            NIs=[I],
            NBs=[B]
        )
    ;
        NIs=[I|MIs],
        NBs=[B|MBs],
        removeIndxs_simple(Is,Bs,MIs,MBs,Changed)
    ).
removeIndxs_simple([],[],[],[],_):-!.
removeIndxs_simple([],_,[],[],1):-!.
removeIndxs_simple(Indx,[],[],[],1):-!,
    litAsgnFalses(Indx).



removeIndxs_ground([I|Is],[B|Bs],Z,NIs,NBs,Changed):-
    (ground(I) ->
        Changed=1,
        (I=:= -1 ->
            removeIndxs_ground(Is,Bs,Z,NIs,NBs,_)
        ;
            NIs=[I],
            NBs=[B]
        )
    ;
    ((ground(B), B=:= -Z) ->
        Changed=1,
        litAsgnFalse(I),
        removeIndxs_ground(Is,Bs,Z,NIs,NBs,_)
    ;
        NIs=[I|MIs],
        NBs=[B|MBs],
        removeIndxs_ground(Is,Bs,Z,MIs,MBs,Changed)
    )).
removeIndxs_ground([],[],_,[],[],_):-!.
removeIndxs_ground([],_,_,[],[],1):-!.
removeIndxs_ground(Indx,[],_,[],[],1):-!,
    litAsgnFalses(Indx).

boolElementSimplifyAdv(Constr,NewConstr,Changed):-
    Constr=bc(_Type,[Indx,Bits,Z]),
    (ground(Bits) ->
        splitToOnesAndZeros(Bits,Indx,Ones,Zeros),
        (Zeros = [] ->
            Changed=1,
            NewConstr=none,
            litAsgnTrue(Z) ;
        (Ones = [] ->
            Changed=1,
            NewConstr=none,
            litAsgnFalse(Z) ;
        (Ones = [I1] ->
            Changed=1,
            NewConstr=none,
            litUnify(Z,I1) ;
        (Zeros = [I0] ->
            Changed=1,
            NewConstr=none,
            litUnify(Z,-I0) ;
        NewConstr=Constr
        ))))
    ;
        NewConstr=Constr
    ).

boolElementDecompose(bc(Type,Data),Constrs):-
    Data=[Indx,Bits,Z],
    (ground(Bits) ->
        splitToOnesAndZeros(Bits,Indx,Ones,Zeros),
        bcOr:orType(OrType),
        auxLiterals:lits2plits(Ones,Vec1s),
        auxLiterals:lits2plits(Zeros,Vec0s),
        Constrs=[bc(OrType,[Z|Vec1s]),bc(OrType,[-Z|Vec0s])]
    ;
        Type=[_,_,_|RType],
        NewType=[skipSimplify,skipSimplify,0|RType],
        Constrs=[bc(NewType,Data)]
    ).

splitToOnesAndZeros([B|Bs],[I|Is],I1s,I0s):-!,
    (B=:=1 ->
        I1s=[I|MI1s],
        splitToOnesAndZeros(Bs,Is,MI1s,I0s)
    ;
        I0s=[I|MI0s],
        splitToOnesAndZeros(Bs,Is,I1s,MI0s)
    ).
splitToOnesAndZeros([],[],[],[]):-!.

% --------------------------
% | Encode                 |
% --------------------------
boolElement2cnf(bc(_Type,[Indx,Bits,Z]),CnfH-CnfT):-!,
    ((ground(Z), abs(Z)=:=1) ->
        (Z=:=1 ->
            boolMux_cnf1(Bits,Indx,CnfH-CnfT)
        ;
            boolMux_cnf0(Bits,Indx,CnfH-CnfT)
        )
    ;
        boolMux_cnf(Bits,Indx,Z,CnfH-CnfT)
    ).

boolMux_cnf([X|Xs],[I|Indx],Z,CnfH-CnfT):-!,
    ((ground(X),X=:=  1) ->
        CnfH=[[-I, Z]|CnfM] ;
    ((ground(X),X=:= -1) ->
        CnfH=[[-I, -Z]|CnfM] ;
    CnfH=[
          [-I, -X, Z],
          [-I, X, -Z]
          |CnfM]
    )),
    boolMux_cnf(Xs,Indx,Z,CnfM-CnfT).
boolMux_cnf([],[],_,Cnf-Cnf).

boolMux_cnf1([X|Xs],[I|Indx],CnfH-CnfT):-!,
    ((ground(X),X=:=1) -> CnfH=CnfT ;
    CnfH=[
          [-I, X]
          |CnfM]),
    boolMux_cnf1(Xs,Indx,CnfM-CnfT).
boolMux_cnf1([],[],Cnf-Cnf).
boolMux_cnf0([X|Xs],[I|Indx],CnfH-CnfT):-!,
    ((ground(X),X=:= -1) -> CnfH=CnfT ;
    CnfH=[
          [-I, -X]
          |CnfM]),
    boolMux_cnf0(Xs,Indx,CnfM-CnfT).
boolMux_cnf0([],[],Cnf-Cnf).







%%% --------------------------- %%%
%%% Decompose Matrix[Index]=Vec %%%
%%% --------------------------- %%%

decomposeBoolArraysElements(Indx,Matrix,Vector,ConstrsH-ConstrsT):-!,
    bcInteger:getDirectNumber(Indx,(Min,Max,IBits,_)),
    (Min==0 ->
        decomposeBoolArraysElements_0(IBits,Max,Matrix,Vector,ConstrsH-ConstrsT) ;
    (Min>0 ->
        (auxLists:listDropFrom(Min,Matrix,RMatrix)->
            NMax is Max - Min,
            decomposeBoolArraysElements_0(IBits,NMax,RMatrix,Vector,ConstrsH-ConstrsT) ;
            throw(unsat)) ;
    %Min<0 ->
        Drop is abs(Min),
        (auxLists:listSplit(Drop,IBits,Falses,NIBits)->
            auxLiterals:litAsgnFalses(Falses),
            decomposeBoolArraysElements_0(NIBits,Max,Matrix,Vector,ConstrsH-ConstrsT) ;
            throw(unsat))
    )).

decomposeBoolArraysElements_0(IBits,Max,Matrix,Vector,ConstrsH-ConstrsT):-!,
    length(Matrix,N1),
    N is N1 - 1,
    (N==Max ->
        decomposeBoolArraysElements_1(Matrix,IBits,Vector,ConstrsH-ConstrsT) ;
    (N < Max ->
        (auxLists:listSplit(N,IBits,NIBits,Falses) ->
            auxLiterals:litAsgnFalses(Falses),
            decomposeBoolArraysElements_1(Matrix,NIBits,Vector,ConstrsH-ConstrsT) ;
            throw(unsat)) ;
    %(N > Max ->
        (auxLists:listKeepFrom(Max,Matrix,RMatrix,_) ->
            decomposeBoolArraysElements_1(RMatrix,IBits,Vector,ConstrsH-ConstrsT) ;
            throw(unsat))
    )).

decomposeBoolArraysElements_1(Matrix,IBits,Vector,ConstrsH-ConstrsT):-!,
    getMaxLength(Matrix,0,MaxLen),!,
    length(NVector,MaxLen),
    auxLiterals:litUnifiesWfalses(Vector,NVector),!,
    bcBoolElement:boolElementType(Type),
    decomposeBoolArraysElements_2(NVector,Matrix,IBits,Type,ConstrsH-ConstrsT).
    
decomposeBoolArraysElements_2([Z|Vector],Matrix,IBits,Type,ConstrsH-ConstrsT):-!,
    collectColumn(Matrix,Column,RMatrix),
    ConstrsH=[bc(Type,[IBits,Column,Z])|ConstrsM],!,
    decomposeBoolArraysElements_2(Vector,RMatrix,IBits,Type,ConstrsM-ConstrsT).
decomposeBoolArraysElements_2([],_,_,_,Constrs-Constrs):-!.

getMaxLength([],MaxLen,MaxLen):-!.
getMaxLength([R|Matrix],CLen,MaxLen):-!,
    length(R,RLen),
    (RLen > CLen ->
        getMaxLength(Matrix,RLen,MaxLen)
    ;
        getMaxLength(Matrix,CLen,MaxLen)
    ).
    
    
collectColumn([],[],[]):-!.
collectColumn([[X|R]|Matrix],[X|Column],[R|RMatrix]):-!,
    collectColumn(Matrix,Column,RMatrix).
collectColumn([[]|Matrix],[-1|Column],[[]|RMatrix]):-!,
    collectColumn(Matrix,Column,RMatrix).
