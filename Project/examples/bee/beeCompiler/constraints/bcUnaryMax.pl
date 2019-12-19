% Author: Amit Metodi
% Last Update: 22/08/2012

:- module(bcUnaryMax, [ ]).
:- use_module('../auxs/auxLiterals').

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=int_max(A,B,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcInteger:getUnaryNumber(A,Au),
       bcInteger:getUnaryNumber(B,Bu),
       bcInteger:getUnaryNumber(Z,Zu),
       bcUnaryMax:unaryMaxType(Type),
       bcUnaryMax:unaryMaxSimplify(bc(Type,[Zu,Au,Bu]),Constr,1),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_array_max(As,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcInteger:getUnaryNumbers(As,Asu),
       bcInteger:getUnaryNumber(Z,Zu),
       bcUnaryMax:unaryMaxType(Type),
       bcUnaryMax:unaryMaxSimplify(bc(Type,[Zu|Asu]),Constr,1),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).


%%% min(A,B,C) = max(-A,-B,-C)
:- Head=int_min(A,B,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bParser:int_max(-A,-B,-Z,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_array_min(As,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcUnaryMax:negNumbers(As,NAs),
       bParser:int_array_max(NAs,-Z,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

negNumbers([A|As],[-A|NAs]):-!,
    negNumbers(As,NAs).
negNumbers([],[]):-!.

%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
unaryMaxType([
        bcUnaryMax:unaryMaxSimplify,
        bcUnaryMax:unaryMaxSimplifyAdv,
        bcUnaryMax:unaryMaxDecompose,
        0,
        unaryMax
       ]):-!.



%%% ---------- %%%
%%%  Simplify  %%%
%%% ---------- %%%
unaryMaxSimplify(Constr,NewConstr,Changed):-!,
    Constr=bc(Type,[Z|As]),
    auxUnarynum:unarynumIsRangeChanged(Z,Z0,Changed),!,
    unaryMaxSimplify_zNas(Z0,As,NZ,NAs,Changed),
    (NAs=[] -> throw(unsat) ;
    (NAs=[A] ->
        Changed=1,
        NewConstr=none,
        auxUnarynum:unarynumEquals(A,NZ) ;
    (NZ=(Zval,Zval,_) ->
        Changed=1,
        atLeastOneIsZ(NAs,Zval,NewConstr) ;
    (Changed==1 ->
        NewConstr=bc(Type,[NZ|NAs])
    ;
        NewConstr=Constr
    )))).

unaryMaxSimplify_zNas(Z,As,NZ,NAs,Changed):-
    Z=(Zmin,Zmax,_),
    unaryMaxSimplify_as(As,Zmin,Zmax,NAs,NZmin,NZmax,Changed),
    ((Zmin==NZmin, Zmax==NZmax) ->
        NZ=Z
    ;
        Changed=1,
        auxUnarynum:unarynumSetMin(Z,NZmin,Z1),
        auxUnarynum:unarynumSetMax(Z1,NZmax,NZ)
    ).
    
unaryMaxSimplify_as(As,Zmin,Zmax,NAs,NZmin,NZmax,Changed):-
    (As=[(A0min,_)|_] ->
        AsMin is max(A0min,Zmin - 1),
        updateAs(As,AsMin,AsMin,Zmax,As0,(TZmin,TZmax),Changed),
        (TZmin > AsMin ->
            updateAs(As0,TZmin,TZmin,TZmax,NAs,(FZmin,NZmax),Changed),
            NZmin is max(FZmin,Zmin)
        ;
            NZmin is max(TZmin,Zmin),
            NZmax=TZmax,
            (Changed==1 ->
                NAs=As0
            ;
                NAs=As
            )
        )
    ;
        throw(unsat)
    ).


updateAs([A|As],AsMin,AsMax,Zmax,NAs,ZMnM,Changed):-!,
    auxUnarynum:unarynumIsRangeChanged(A,NA,Changed),
    updateA(NA,AsMin,Zmax,FA,Changed),!,
    (FA==none ->
        updateAs(As,AsMin,AsMax,Zmax,NAs,ZMnM,Changed)
    ;
        FA=(Amin,Amax,_),
        NAsMin is max(Amin,AsMin),
        NAsMax is max(Amax,AsMax),
        NAs=[FA|MAs],
        updateAs(As,NAsMin,NAsMax,Zmax,MAs,ZMnM,Changed)
    ).
updateAs([],AsMin,AsMax,_,[],(AsMin,AsMax),_):-!.


updateA(A,AsMin,Zmax,FA,Changed):-
    A=(Amin,Amax,_),
    (Amax < AsMin -> Changed=1, FA=none ;
    ((AsMin =< Amin , Amax =< Zmax) -> FA=A ;
    (Zmax < Amin -> throw(unsat) ;
    (AsMin > Amin ->
        Changed=1,
        auxUnarynum:unarynumFocusOn(A,AsMin,Amax,NA),
        updateA(NA,AsMin,Zmax,FA,_) ;
%    (Amax > Zmax ->
        Changed=1,
        auxUnarynum:unarynumSetMax(A,Zmax,NA),
        updateA(NA,AsMin,Zmax,FA,_)
    )))).



% ----- special case - Z is constant ----- %
atLeastOneIsZ(As,Zval,Constr):-!,
    Zval1 is Zval - 1,
    atLeastOneIsZ_(As,Zval1,Zval,Bits),!,
    bcAtLeastOne:aloType(Type),
    auxLiterals:lits2plits(Bits,Vec),
    bcAtLeastOne:aloSimplify(bc(Type,Vec),Constr,_).

atLeastOneIsZ_([(Zval1,Zval,_,Lbit)|As],Zval1,Zval,[Lbit|Bits]):-!,
    atLeastOneIsZ_(As,Zval1,Zval,Bits).
atLeastOneIsZ_([(Zval,Zval,_)|_],_,Zval,[1]):-!.
atLeastOneIsZ_([(Zval1,Zval1,_)|As],Zval1,Zval,Bits):-!,
    atLeastOneIsZ_(As,Zval1,Zval,Bits).
atLeastOneIsZ_([],_,_,[]):-!.


% ----- Advance Simplfy ----- %
unaryMaxSimplifyAdv(Constr,NewConstr,Changed):-!,
    Constr=bc(Type,[Z|As]),
    (As=[] -> throw(unsat) ;
    As=[(Amin,_)|_],
    removeConstsEqVal(As,Amin,NAs,Changed),
    Z=(Zmin,Zmax,_),
    (NAs=[] ->
        (Amin==Zmin ->
            NewConstr=none
        ; % Amin+1=Zmin
            throw(unsat)
        ) ;
    (NAs=[A0] ->
        Changed=1,
        NewConstr=none,
        auxUnarynum:unarynumEquals(A0,Z) ;
    (findUniqueRange(NAs,Zmin,Zmax,RNAs,ShareWithA,ShareStartAt) ->
        unifySharedRange(Z,ShareWithA,ShareStartAt,NZ,NA),
        Changed=1,
        (NZ=(Zval,Zval,_) ->
            atLeastOneIsZ([NA|RNAs],Zval,NewConstr)
        ;
            NewConstr=bc(Type,[NZ,NA|RNAs])
        )
    ;
    (Changed==1 ->
        NewConstr=bc(Type,[Z|NAs])
    ;
        NewConstr=Constr
    ))))).


removeConstsEqVal([(Val,Val,_)|As],Val,NAs,1):-!,
    removeConstsEqVal(As,Val,NAs,1).
removeConstsEqVal([A|As],Val,[A|NAs],Changed):-!,
    removeConstsEqVal(As,Val,NAs,Changed).
removeConstsEqVal([],_,[],_):-!.



findUniqueRange([A|As],RestAsMax,Zmax,RestAs,EndWithZmax,ShareStartAt):-!,
    A=(_,Amax,_),
    (Amax==Zmax ->
        !,var(EndWithZmax),!,
        EndWithZmax=A,
        findUniqueRange(As,RestAsMax,Zmax,RestAs,EndWithZmax,ShareStartAt)
    ;
        RestAsMax1 is max(RestAsMax,Amax),
        RestAs=[A|MRestAs],
        findUniqueRange(As,RestAsMax1,Zmax,MRestAs,EndWithZmax,ShareStartAt)
    ).
findUniqueRange([],ShareStartAt,_,[],EndWithZmax,ShareStartAt):-!,
    \+ var(EndWithZmax).



unifySharedRange((Zmin,_,Zbits,_),(Amin,_,Abits,_),NewMax,(Zmin,NewMax,NZbits,NZlbit),(Amin,NewMax,NAbits,NAlbit)):-!,
    Zlen is NewMax - Zmin,
    (Zlen > 0 ->
        splitNumberRange(Zlen,Zbits,NZbits,NZlbit,RZbits)
    ;
        NZlbit=1,
        NZbits=[],
        RZbits=Zbits
    ),
    Alen is NewMax - Amin,
    splitNumberRange(Alen,Abits,NAbits,NAlbit,RAbits),!,
    auxLiterals:litUnifies(RZbits,RAbits).


splitNumberRange(1,[LB|RBits],[LB],LB,RBits):-!.
splitNumberRange(2,[B1,LB|RBits],[B1,LB],LB,RBits):-!.
splitNumberRange(3,[B1,B2,LB|RBits],[B1,B2,LB],LB,RBits):-!.
splitNumberRange(4,[B1,B2,B3,LB|RBits],[B1,B2,B3,LB],LB,RBits):-!.
splitNumberRange(5,[B1,B2,B3,B4,LB|RBits],[B1,B2,B3,B4,LB],LB,RBits):-!.
splitNumberRange(Keep,[B1,B2,B3,B4,B5|Bits],[B1,B2,B3,B4,B5|NBits],NLBit,RBits):-!,
   Keep1 is Keep - 5,
   splitNumberRange(Keep1,Bits,NBits,NLBit,RBits).


%%% ----------- %%%
%%%  Decompose  %%%
%%% ----------- %%%
unaryMaxDecompose(bc(_Type,[Z|As]),Constrs):-!,
    fixInts2collect(As,As1),!,
    Z=(Zmin,_,ZBits,_),
    bcOr:orType(OrType),
    (As=[(Zmin,_)|_] ->
        generateOrConstraints(ZBits,Zmin,As1,OrType,Constrs)
    ;
        Zmin1 is Zmin - 1,
        collectBits_vali(As1,Zmin1,Zmin,ALObits,As2),!,
        bcAtLeastOne:aloType(ALOType),
        auxLiterals:lits2plits(ALObits,ALOVec),!,
        Constrs=[bc(ALOType,ALOVec)|MConstrs],
        generateOrConstraints(ZBits,Zmin,As2,OrType,MConstrs)
    ).



fixInts2collect([(Min,_,Bits,_)|As],[(Min,Bits)|CAs]):-!,
    fixInts2collect(As,CAs).
fixInts2collect([],[]):-!.

collectBits_vali([(I,[Bi])|As],I,I1,[Bi|Bits],RAs):-!,
    collectBits_vali(As,I,I1,Bits,RAs).
collectBits_vali([(I,[Bi|Bs])|As],I,I1,[Bi|Bits],[(I1,Bs)|RAs]):-!,
    collectBits_vali(As,I,I1,Bits,RAs).
collectBits_vali([],_,_,[],[]):-!.


generateOrConstraints([Zi|ZBits],I,As,OrType,[bc(OrType,[Zi|OrVec])|MConstrs]):-!,
    I1 is I + 1,
    collectBits_vali(As,I,I1,Bs,RAs),!,
    auxLiterals:lits2plits(Bs,OrVec),
    generateOrConstraints(ZBits,I1,RAs,OrType,MConstrs).
generateOrConstraints([],_,[],_,[]):-!.
