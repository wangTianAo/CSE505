% Author: Amit Metodi
% Last Updated: 20/09/2015

:- module(bcUnaryArrayEq, [ ]).
:- use_module('../auxs/auxLiterals').

:- Head=int_arrays_eq(As,Bs,Constrs-Constrs),
   Body=(
       !,
       bcUnaryArrayEq:unifyNumberArrays(As,Bs)
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_arrays_neq(As,Bs,ConstrsH-ConstrsT),
   Body=(
       !,
       bcUnaryArrayEq:decomposeUnaryArrayNEqReif(As,Bs,1,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_arrays_eq_reif(As,Bs,R,ConstrsH-ConstrsT),
   Body=(
       !,
       bcUnaryArrayEq:decomposeUnaryArrayEqReif(As,Bs,R,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_arrays_neq_reif(As,Bs,R,ConstrsH-ConstrsT),
   Body=(
       !,
       bcUnaryArrayEq:decomposeUnaryArrayNEqReif(As,Bs,R,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

%%% ------------------------- %%%
%%% Decompose                 %%%
%%% ------------------------- %%%
unifyNumberArrays([A|As],[B|Bs]):-!,
    bcInteger:unifyNumbers(A,B),!,
    unifyNumberArrays(As,Bs).
unifyNumberArrays([],[]):-!.
unifyNumberArrays([A|As],[]):-!,
    bcInteger:unifyNumbers(A,0),!,
    unifyNumberArrays(As,[]).
unifyNumberArrays([],[B|Bs]):-!,
    bcInteger:unifyNumbers(0,B),!,
    unifyNumberArrays([],Bs).
   
%%% ------------------------- %%%
%%% Decompose                 %%%
%%% ------------------------- %%%

:- if(bSettings:intArraysDiff(decomposeDiff)).

decomposeUnaryArrayEqReif(As,Bs,R,ConstrsH-ConstrsT):-!,
    decomposeUnaryArrayNEqReif(As,Bs,-R,ConstrsH-ConstrsT).
decomposeUnaryArrayNEqReif(As,Bs,R,ConstrsH-ConstrsT):-
    extractNEQreifs(As,Bs,Rs,ConstrsH-ConstrsM),
    bParser:bool_array_or_reif(Rs,R,ConstrsM-ConstrsT).
        
extractNEQreifs([A|As],[B|Bs],[R|Rs],ConstrsH-ConstrsT):-
    bParser:int_neq_reif(A,B,R,ConstrsH-ConstrsM),!,
    extractNEQreifs(As,Bs,Rs,ConstrsM-ConstrsT).
extractNEQreifs([],[],[],Constrs-Constrs):-!.
extractNEQreifs([A|As],[],[R|Rs],ConstrsH-ConstrsT):-
    bParser:int_neq_reif(A,0,R,ConstrsH-ConstrsM),!,
    extractNEQreifs(As,[],Rs,ConstrsM-ConstrsT).
extractNEQreifs([],[B|Bs],[R|Rs],ConstrsH-ConstrsT):-
    bParser:int_neq_reif(0,B,R,ConstrsH-ConstrsM),!,
    extractNEQreifs([],Bs,Rs,ConstrsM-ConstrsT).

:- else.

decomposeUnaryArrayNEqReif(As,Bs,R,ConstrsH-ConstrsT):-!,
    decomposeUnaryArrayEqReif(As,Bs,-R,ConstrsH-ConstrsT).

decomposeUnaryArrayEqReif(As,Bs,R,ConstrsH-ConstrsT):-
    length(As,Sz),!,
    length(Bs,Sz),!,
    (Sz =:= 0 ->
        litAsgnFalse(R),
        ConstrsH=ConstrsT ;
    (Sz =:= 1 ->
        As=[A],
        Bs=[B],
        bParser:int_eq_reif(A,B,R,ConstrsH-ConstrsT) ;
    unaryEqLinkType(Type),
    decomposeUnaryArrayEqReif(As,Bs,1,R,Type,ConstrsH-ConstrsT))).

decomposeUnaryArrayEqReif([A|As],[B|Bs],P,R,Type,ConstrsH-ConstrsT):-!,
    bcInteger:getUnaryNumber(A,Au),
    bcInteger:getUnaryNumber(B,Bu),
    Constr=bc(Type,[P,TR,Au,Bu]),
    unaryEqLinkSimplify(Constr,NewConstr,1),
    (NewConstr == none ->
        ConstrsH=ConstrsM
    ;
        ConstrsH=[NewConstr|ConstrsM]
    ),!,
    decomposeUnaryArrayEqReif(As,Bs,TR,R,Type,ConstrsM-ConstrsT).
decomposeUnaryArrayEqReif([],[],TR,R,_,Constrs-Constrs):-!,
    litUnify(TR,R).


%%% ------------------------- %%%
%%% P => ((A==B)==R)          %%%
%%% !P => !R                  %%%
%%% ------------------------- %%%
unaryEqLinkType([
                   bcUnaryArrayEq:unaryEqLinkSimplify,
                   skipSimplify,
                   0,
                   bcUnaryArrayEq:unaryEqLink2cnf,
                   unaryEqLink]).

unaryEqLinkSimplify(Constr,NewConstr,Changed):-!,
    Constr=bc(Type,[P,R,A,B]),
    (ground(P) ->
        Changed=1,
        (P =:= 1 ->
            bcUnaryDiffReif:unaryDiffReifType(DiffType),
            bcUnaryDiffReif:unaryDiffReifSimplify(bc(DiffType,[-R,A,B]),NewConstr, 1)
        ;
            NewConstr=none,
            litAsgnFalse(R)
        )
    ;
    ((ground(R), R =:= 1) ->
        Changed=1,
        NewConstr=none,
        litAsgnTrue(P),
        auxUnarynum:unarynumEquals(A,B)
    ;
    auxUnarynum:unarynumIsRangeChanged(A,NA,Changed),
    auxUnarynum:unarynumIsRangeChanged(B,NB,Changed),
    (Changed==1 ->
        NA=(Amin,Amax,_),
        NB=(Bmin,Bmax,_),
        ((Amin>Bmax ; Amax<Bmin) ->
            litAsgnFalse(R),
            NewConstr=none ;
        (Amin==Bmin ->
            Dmin=Amin
        ;
            Dmin is max(Amin,Bmin) - 1
        ),
        (Amax==Bmax ->
            Dmax=Amax
        ;
            Dmax is min(Amax,Bmax) + 1
        ),
        auxUnarynum:unarynumFocusOn(NA,Dmin,Dmax,FA),
        auxUnarynum:unarynumFocusOn(NB,Dmin,Dmax,FB),
        NewConstr=bc(Type,[P,R,FA,FB])
        ) ;
    NewConstr=Constr
    ))).

unaryEqLink2cnf(bc(_Type,[P,R,A,B]),CnfH-CnfT):-!,
    A=(Amin,_,Abits,_),
    B=(Bmin,_,Bbits,_),
    (Amin==Bmin ->
        bcVectorDiffReif:implyVectorEqReif(Abits,Bbits,P,R,CnfH-CnfT) ;
    (Amin<Bmin ->
        Amin+1 =:= Bmin,!,
        bcVectorDiffReif:implyVectorEqReif(Abits,[1|Bbits],P,R,CnfH-CnfT) ;
    %Amin>Bmin ->
        Amin =:= Bmin+1,!,
        bcVectorDiffReif:implyVectorEqReif([1|Abits],Bbits,P,R,CnfH-CnfT)
    )).

:- endif.