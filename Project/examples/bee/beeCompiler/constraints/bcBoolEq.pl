% Author: Amit Metodi
% Last Updated: 12/03/2016

:- module(bcBoolEq, [ ]).
:- use_module('../auxs/auxLiterals').

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=bool_array_eq_reif(Bs,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       (Bs=[] ->
           ConstrsH=ConstrsT,
           auxLiterals:litAsgnTrue(Z) ;
       bcBoolEq:boolEqType(EqType),
       auxLiterals:lits2plits(Bs,EqVec),
       bcBoolEq:boolEqSimplify(bc(EqType,[Z|EqVec]),Constr,1),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       ))
   ),
   bParser:addConstraint(Head,Body).

%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
boolEqType([
        bcBoolEq:boolEqSimplify,
        skipSimplify,
        0,
        bcBoolEq:boolArrayEq2cnf,
        boolArrayEq
       ]):-!.

%%% ----------- %%%
%%%  Simplify   %%%
%%% ----------- %%%
%%% [Z|Vec] Z=literal , Vec=[PureLit,...,PureLit]
boolEqSimplify(Constr,NewConstr,Changed):-!,
    Constr=bc(Type,[Z|Vec]),
    ((ground(Z), Z =:= 1) ->
        Vec=[X1|Xs],
        plitsUnify(Xs,X1),
        NewConstr=none ;
    simplifyBoolEqArray(Vec, NewVec, FoundOne, FoundZero, Changed),
    (Changed==1 ->
        (FoundOne==1 ->
            (FoundZero==1 ->
                litAsgnFalse(Z),
                NewConstr=none
            ;
                auxLiterals:plitNotXs(NewVec,NotVec),
                bcOr:orType(OrType),
                bcOr:orSimplify(bc(OrType,[-Z|NotVec]),NewConstr,_)
            ) ;
        (FoundZero==1 ->
            bcOr:orType(OrType),
            bcOr:orSimplify(bc(OrType,[-Z|NewVec]),NewConstr,_) ;
        (NewVec=[] ->
            %% SHOULD NOT HAPPEN
            throw(bug(simplify,simplifyBoolEqArray(Vec))) ;
        (NewVec=[_] -> % Single var is always equal to the others :)
            litAsgnTrue(Z),
            NewConstr=none ;
        (NewVec=[_,_] ->
            bcXor:xorType(XorType),
            bcXor:xorVecSimplify(bc(XorType,[(Z,1)|NewVec]),NewConstr,_) ;
        NewConstr = bc(Type,[Z|NewVec])
        ))))) ;
        NewConstr = Constr
    )).
        
plitsUnify([X2|Xs],X1):-!,
    auxLiterals:plitUnify(X1,X2),
    plitsUnify(Xs,X1).
plitsUnify([],_):-!.


simplifyBoolEqArray(Pbits,NewPbits,FoundOne,FoundZero,Changed):-!,
    simplifyBoolEqArray(Pbits,TPbits,FoundOne,FoundZero,Changed,NeedSort),
    ((FoundOne==1,FoundZero==1) -> 
        Changed=1,
        NewPbits=[] ;
    (NeedSort==1 ->
        sort(TPbits,TPbits2),
        Changed=1,
        simplifyBoolEqArray(TPbits2,NewPbits,FoundOne,FoundZero,_) ;
    NewPbits=TPbits
    )).

simplifyBoolEqArray([PX1|PWbits],NewPWbits,FoundOne,FoundZero,Changed,NeedSort):-!,
    PX1=(X1,Xop1),
    (ground(X1) ->
        Changed=1,
        (X1*Xop1 =:= 1 ->
            FoundOne=1
        ;
            FoundZero=1
        ),
        simplifyBoolEqArray(PWbits,NewPWbits,FoundOne,FoundZero,Changed,NeedSort) ;
    (var(X1) ->
        simplifyBoolEqArray(PWbits,PX1,NewPWbits,FoundOne,FoundZero,Changed,NeedSort) ;
    lit2plit(X1,X1n,X1op),
    Xop1n is Xop1 * X1op,
    simplifyBoolEqArray(PWbits,(X1n,Xop1n),NewPWbits,FoundOne,FoundZero,Changed,NeedSort)
    )).
simplifyBoolEqArray([],[],_,_,_,_):-!.

simplifyBoolEqArray([PX2|PWbits],PX1,NewPWbits,FoundOne,FoundZero,Changed,NeedSort):-!,
    PX2=(X2,X2op),
    (ground(X2) ->
        Changed=1,
        (X2*X2op =:= 1 ->
            FoundOne=1
        ;
            FoundZero=1
        ),
        simplifyBoolEqArray(PWbits,PX1,NewPWbits,FoundOne,FoundZero,Changed,NeedSort) ;
    (var(X2) ->
        PX1=(X1,X1op),
        (X2 == X1 ->
            Changed=1,
            (X2op==X1op ->
                simplifyBoolEqArray(PWbits,PX1,NewPWbits,FoundOne,FoundZero,Changed,NeedSort)
            ;
                FoundOne=1,
                FoundZero=1
            )
        ;
            (X2 @< X1 ->
                NeedSort=1,
                NewPWbits=[PX2|MorePWbits],
                simplifyBoolEqArray(PWbits,PX1,MorePWbits,FoundOne,FoundZero,Changed,NeedSort)
            ;
                NewPWbits=[PX1|MorePWbits],
                simplifyBoolEqArray(PWbits,PX2,MorePWbits,FoundOne,FoundZero,Changed,NeedSort)
            )
        )
    ;
        lit2plit(X2,X2n,X2opb),
        X2opn is X2op*X2opb,
        simplifyBoolEqArray([(X2n,X2opn)|PWbits],PX1,NewPWbits,FoundOne,FoundZero,Changed,NeedSort)
    )).

simplifyBoolEqArray([],PWx,[PWx],_,_,_,_):-!.

        
%%% ----------- %%%
%%%    Encode   %%%
%%% ----------- %%%
boolArrayEq2cnf(bc(_,[Z|Vec]),CnfH-CnfT):-!,
    plits2lits(Vec,Xs),
    litNotXs(Xs,NXs),
    length(Xs,N),!,
    (ground(Z) ->
        (Z =:= -1 ; throw(bug(encode,boolArrayEq2cnf(Z,Vec)))),
        % at_least_one 0 in Xs
        bcAtLeastOne:atLeastOne2clauses(NXs,N,CnfH-CnfM),
        % at_least_one 1 in Xs
        bcAtLeastOne:atLeastOne2clauses(Xs,N,CnfM-CnfT) 
    ;
    % Z -> (Xi==Xj)
    boolArrayEq2cnf_aux(Xs,Z,CnfH-Cnf1),
    N1 is N + 1,
    % !Z -> at_least_one 0 in Xs
    bcAtLeastOne:atLeastOne2clauses([Z|NXs],N1,Cnf1-Cnf2),
    % !Z -> at_least_one 1 in Xs
    bcAtLeastOne:atLeastOne2clauses([Z|Xs],N1,Cnf2-CnfT)
    ).

:- if(bSettings:boolArrayEq(simple)).

boolArrayEq2cnf_aux(Xs,Z,CnfH-CnfT):-
    append(_,[Xlast],Xs),
    % Z -> (Xn -> X1)
    % Z -> (Xi -> Xi+1)
    boolArrayEq2cnf_aux(Xs,-Z,Xlast,CnfH-CnfT).

boolArrayEq2cnf_aux([X1|Xs],NZ,X0,[[NZ,-X0,X1]|CnfH]-CnfT):-
    boolArrayEq2cnf_aux(Xs,NZ,X1,CnfH-CnfT).
boolArrayEq2cnf_aux([],_NZ,_X0,Cnf-Cnf):-!.

:- elif(bSettings:boolArrayEq(arc)).

boolArrayEq2cnf_aux([_],_Z,Cnf-Cnf):-!.
boolArrayEq2cnf_aux([X0|Xs],Z,CnfH-CnfT):-
    boolArrayEq2cnf_aux(Xs,-Z,X0,CnfH-CnfM),
    boolArrayEq2cnf_aux(Xs,Z,CnfM-CnfT).

boolArrayEq2cnf_aux([Xi|Xs],NZ,X0,[[NZ,X0,-Xi],[NZ,-X0,Xi]|CnfH]-CnfT):-
    boolArrayEq2cnf_aux(Xs,NZ,X0,CnfH-CnfT).
boolArrayEq2cnf_aux([],_NZ,_X0,Cnf-Cnf):-!.

:- elif(bSettings:boolArrayEq(old)).
%% the first encoding released - arc-consistent only with the first variable

boolArrayEq2cnf_aux([X0|Xs],Z,CnfH-CnfT):-
    boolArrayEq2cnf_aux(Xs,-Z,X0,CnfH-CnfT).

boolArrayEq2cnf_aux([Xi|Xs],NZ,X0,[[NZ,X0,-Xi],[NZ,-X0,Xi]|CnfH]-CnfT):-
    boolArrayEq2cnf_aux(Xs,NZ,X0,CnfH-CnfT).
boolArrayEq2cnf_aux([],_NZ,_X0,Cnf-Cnf):-!.

:- else.
:- bSettings:boolArrayEq(X), writef('ERROR: "%w" is wrong value for bSettings:boolArrayEq !\n',[X]),flush_output,halt.
:- endif.