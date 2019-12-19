% Author: Amit Metodi
% Last Updated: 23/09/2015

:- module(bcUnaryLex, [ ]).
:- use_module('../auxs/auxLiterals').


/*
TODO:
unaryLexLinkSimplify when:
* PrevEq==1 & Amin<Bmin (Amin+1==Bmin after prop)
  Then "new"PrevEq=A[Amin] and focus from Bmin.

  bc(Type, [ (2, n, [A3, A4, ...], An), (3, n, [B4, ...], Bn), 1, MeEq])
  ->
  bc(Type, [ (3, n, [A4, ...], An), (3, n, [B4, ...], Bn), A3, MeEq])

*/


:- Head=int_arrays_lex(As,Bs,ConstrsH-ConstrsT),
   Body=(
       !,
       bcUnaryLex:unaryLexLinkType(LinkType),
       bcUnaryLex:createLexLinks(As,Bs,1,_,LinkType,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_arrays_lexLt(As,Bs,ConstrsH-ConstrsT),
   Body=(
       !,
       bcUnaryLex:unaryLexLinkType(LinkType),
       bcUnaryLex:createLexLinks(As,Bs,1,-1,LinkType,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_arrays_lex_reif(As,Bs,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bParser:int_arrays_lex_implied(As,Bs,Z,ConstrsH-ConstrsM),
       bParser:int_arrays_lexLt_implied(Bs,As,-Z,ConstrsM-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_arrays_lexLt_reif(As,Bs,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bParser:int_arrays_lexLt_implied(As,Bs,Z,ConstrsH-ConstrsM),
       bParser:int_arrays_lex_implied(Bs,As,-Z,ConstrsM-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_arrays_lex_implied(As,Bs,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcUnaryLex:unaryLexLinkType(LinkType),
       bcUnaryLex:createLexLinks(As,Bs,Z,_,LinkType,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_arrays_lexLt_implied(As,Bs,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcUnaryLex:unaryLexLinkType(LinkType),
       bcUnaryLex:createLexLinks(As,Bs,Z,-1,LinkType,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).
   
%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
unaryLexLinkType([
              bcUnaryLex:unaryLexLinkSimplify,
              skipSimplify,
              0,
              bcUnaryLex:unaryLexLink2cnf,
              unaryLexLink
             ]).


%%% ------------------------- %%%
%%% build lex link chain      %%%
%%% ------------------------- %%%

createLexLinks([A],[B],PrevEq,LastEq,Type,ConstrsH-ConstrsT):-!,
    bcInteger:getUnaryNumber(A,Au),
    bcInteger:getUnaryNumber(B,Bu),
    unaryLexLinkSimplify(bc(Type,[Au,Bu,PrevEq,LastEq]), Constr, 1),
    (Constr==none ->
        ConstrsH=ConstrsT
    ;
        ConstrsH=[Constr|ConstrsT]
    ).
createLexLinks([A|As],[B|Bs],PrevEq,LastEq,Type,ConstrsH-ConstrsT):-!,
    bcInteger:getUnaryNumber(A,Au),
    bcInteger:getUnaryNumber(B,Bu),
    unaryLexLinkSimplify(bc(Type,[Au,Bu,PrevEq,MeEq]), Constr, 1),
    (Constr==none ->
        createLexLinks(As,Bs,MeEq,LastEq,Type,ConstrsH-ConstrsT)
    ;
        ConstrsH=[Constr|ConstrsM],
        createLexLinks(As,Bs,MeEq,LastEq,Type,ConstrsM-ConstrsT)
    ).
createLexLinks([],[],PrevEq,LastEq,_,Constrs-Constrs):-!,
    litUnify(PrevEq,LastEq).

/*
   PrevEq -> (A<=B AND (A=B -> MeEq))
   !PrevEq -> !MeEq
*/
% --------------------------------
% | Simplify (A <= B)            |
% --------------------------------
unaryLexLinkSimplify(Constr, NewConstr, Changed):-!,
    Constr=bc(Type,[A,B,PrevEq,MeEq]),
    ((ground(PrevEq),PrevEq=:= -1) -> % don't care
        Changed=1,
        NewConstr=none,!,
        litAsgnFalse(MeEq)
    ;
    ((ground(MeEq),MeEq=:= 1) -> % A=B
        Changed=1,
        NewConstr=none,!,
        litAsgnTrue(PrevEq),
        auxUnarynum:unarynumEquals(A,B)
    ;
    ((ground(PrevEq), ground(MeEq)) -> % PrevEq=1,MeEq=-1  =>  A<B
        Changed=1,
        auxUnarynum:unarynumAddConst(A,1,A1),
        bcUnaryLEq:unaryLEqType(LEqType),!,
        bcUnaryLEq:unaryLEqSimplify(bc(LEqType,[A1,B]), NewConstr, 1)
    ;
    (ground(PrevEq) -> % A<=B
        auxUnarynum:unarynumIsRangeChanged(A,NA,Changed),
        auxUnarynum:unarynumIsRangeChanged(B,NB,Changed),!,
        unaryLexLink_prop(NA,NB,FA,FB,Changed),!,
        (unaryLexLink_drop(FA,FB,PrevEq,MeEq) -> Changed=1, NewConstr=none ;
        (unaryLexLink_replace(FA,FB,PrevEq,MeEq,NewConstr) -> Changed=1 ;
        (Changed==1 -> unaryLexLinkSimplify(bc(Type,[FA,FB,PrevEq,MeEq]), NewConstr, _)
         ;
             NewConstr=Constr
         )))
    ;   % can only focus A,B
        auxUnarynum:unarynumIsRangeChanged(A,NA,Changed),
        auxUnarynum:unarynumIsRangeChanged(B,NB,Changed),!,
        unaryLexLink_focus(NA,NB,FA,FB,Changed),!,
        (unaryLexLink_drop(FA,FB,PrevEq,MeEq) -> Changed=1, NewConstr=none ;
        (unaryLexLink_replace(FA,FB,PrevEq,MeEq,NewConstr) -> Changed=1 ;
        (Changed==1 -> NewConstr=bc(Type,[FA,FB,PrevEq,MeEq])
        ;
            NewConstr=Constr
        )))
    )))).


% A<=B
unaryLexLink_drop(Au,Bu,PrevEq,MeEq):-!,
    Au=(Amin,Amax,_),
    Bu=(Bmin,Bmax,_),
    (Amin > Bmax -> % A > B
        litAsgnFalse(PrevEq),
        litAsgnFalse(MeEq) ;
    (Bmin > Amax -> % A < B
        litAsgnFalse(MeEq) ;
    ((ground(PrevEq), PrevEq=:=1) ->
        (Bmin==Bmax ->
            (Amax\==Bmax -> throw(bug(simplify,unaryLexLink(Au,Bu,PrevEq,MeEq))) ;
            Au=(_,_,_,Albit),!,
            litUnify(MeEq,Albit)
            ) ;
        (Amin==Amax ->
            (Amin\==Bmin -> throw(bug(simplify,unaryLexLink(Au,Bu,PrevEq,MeEq))) ;
            Bu=(Bmin,Bmax,[B1bit|__],_),
            litUnify(MeEq,-B1bit)
            ) ;
        !,fail
        )) ;
    ((Bmin==Bmax,Amin==Amax, Amax==Bmax) ->
        litUnify(PrevEq,MeEq) ;
    !,fail
    )))).

unaryLexLink_replace(Au,Bu,PrevEq,MeEq,Constr):-
    Au=(Amin,Amax,_,Albit),
    Bu=(Bmin,Bmax,_,Blbit),
    (Bmin==Bmax ->
        !,Amin+1=:=Amax,
%     B=[-1] & A=[A0] => (PrevEq=MeEq) & (PrevEq -> -A0)
%     B=[1] & A=[A0] => (-PrevEq or -A0) <-> -MeEq
        (Amin==Bmin ->
            litUnify(PrevEq,MeEq),
            bcAtLeastOne:aloType(ALOType),
            lits2plits([-PrevEq,-Albit],ALOVec),
            bcAtLeastOne:aloSimplify(bc(ALOType,ALOVec),Constr,_)
        ;
            bcOr:orType(OrType),
            lits2plits([-PrevEq,-Albit],OrVec),
            bcOr:orSimplify(bc(OrType,[-MeEq|OrVec]),Constr,_)
        ) ;
    (Amin==Amax ->
        !,Bmin+1=:=Bmax,
%     B=[B0] & A=[-1] => (-PrevEq or B0) <-> -MeEq
%     B=[B0] & A=[ 1] => (PrevEq=MeEq) & (PrevEq -> B0)
        (Amin==Bmax ->
            litUnify(PrevEq,MeEq),
            bcAtLeastOne:aloType(ALOType),
            lits2plits([-PrevEq,Blbit],ALOVec),
            bcAtLeastOne:aloSimplify(bc(ALOType,ALOVec),Constr,_)
        ;
            bcOr:orType(OrType),
            lits2plits([-PrevEq,Blbit],OrVec),
            bcOr:orSimplify(bc(OrType,[-MeEq|OrVec]),Constr,_)
        ) ;
    ((Amin+1=:=Amax, Bmin+1=:=Bmax, Amax==Bmin) ->
%     B=[1,B0] & A=[A0,-1] => (B0 or -A0 or -PrevEq) <-> -MeEq
        bcOr:orType(OrType),
        lits2plits([-PrevEq,Blbit,-Albit],OrVec),
        bcOr:orSimplify(bc(OrType,[-MeEq|OrVec]),Constr,_)
    ;
        fail
    ))).

unaryLexLink_focus(A,B,NA,NB,Changed):-!,
    A=(Amin,Amax,_),
    B=(Bmin,Bmax,_),
    ((Bmax < Amin ; Bmin > Amax) -> NA=A, NB=B ;
    (Amin==Bmin ->
        NAmin=Amin,
        NBmin=Bmin
    ;
        NAmin is max(Amin,Bmin - 1),
        NBmin is max(Bmin,Amin - 1)
    ),
    (Amax==Bmax ->
        NAmax=Amax,
        NBmax=Bmax
    ;
        NAmax is min(Amax, Bmax+1),
        NBmax is min(Bmax, Amax+1)
    ),
    auxUnarynum:unarynumFocusOn(A,NAmin,NAmax,NA,Changed),
    auxUnarynum:unarynumFocusOn(B,NBmin,NBmax,NB,Changed)
    ).

% A<=B
unaryLexLink_prop(A,B,NA,NB,Changed):-!,
    A=(Amin,Amax,_),
    B=(Bmin,Bmax,_),
    (Bmax < Amin -> throw(unsat) ;
    (Bmin > Amax -> NA=A, NB=B ;
    (Amin =< Bmin ; auxUnarynum:unarynumSetMin(B,Amin,_),Changed=1),!,
    (Amax =< Bmax ; auxUnarynum:unarynumSetMax(A,Bmax,_),Changed=1),!,
    DomMin is max(Amin,Bmin-1),
    DomMax is min(Amax+1,Bmax),!,
    auxUnarynum:unarynumFocusOn(A,DomMin,DomMax,NA,Changed),
    auxUnarynum:unarynumFocusOn(B,DomMin,DomMax,NB,Changed)
    )).


% --------------------------------
% | Encoding (A <= B)            |
% --------------------------------
unaryLexLink2cnf(bc(_Type,[A,B,PrevEq,MeEq]), CnfH-CnfT):-!,
    A=(Amin,_,Abits,_),
    B=(Bmin,_,Bbits,_),
    CnfH=[[PrevEq,-MeEq]|CnfM],
    (Amin==Bmin ->
        unaryLexUnary(Abits,Bbits,1,PrevEq,MeEq, CnfM-CnfT) ;
    (Amin > Bmin ->
        Bbits=[B0|MBbits],
        CnfM=[[-PrevEq, B0]| CnfM2],
        unaryLexUnary(Abits,MBbits,1,PrevEq,MeEq, CnfM2-CnfT) ;
    %(Amin < Bmin ->
        Abits=[A0|MAbits],
        CnfM=[[A0, -MeEq]|CnfM2],
        unaryLexUnary(MAbits,Bbits,A0,PrevEq,MeEq, CnfM2-CnfT)
    )).

unaryLexUnary([A|As],[B|Bs],PrevA,PrevEq,MeEq,CnfH-CnfT):-!,
    CnfH=[[-PrevEq, -A, B],
          [A, -B, -MeEq],
          [-PrevEq, B, -PrevA, MeEq]
          | CnfM],
    unaryLexUnary(As,Bs,A,PrevEq,MeEq,CnfM-CnfT).
unaryLexUnary([],[],PrevA,PrevEq,MeEq,CnfH-CnfT):-!,
    CnfH=[[-PrevEq, -PrevA, MeEq]| CnfT].
unaryLexUnary([A],[],PrevA,PrevEq,MeEq,CnfH-CnfT):-!,
    CnfH=[[-PrevEq, -A],
          [-PrevEq, -PrevA, MeEq]
          | CnfT].
unaryLexUnary([],[B],PrevA,PrevEq,MeEq,CnfH-CnfT):-!,
    CnfH=[[-B, -MeEq],
          [-PrevEq, B, -PrevA, MeEq]
          | CnfT].