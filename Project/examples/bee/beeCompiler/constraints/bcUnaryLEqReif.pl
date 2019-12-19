% Components: (A <= B) <-> Z
% Author: Amit Metodi
% Last Updated: 01/07/2012

:- module(bcUnaryLEqReif, [ ]).
:- use_module('../auxs/auxLiterals').

/*
  TODO:
  * advance equi-propagation simplify
*/

:- Head=int_leq_reif(A,B,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcInteger:getUnaryNumber(A,Au),
       bcInteger:getUnaryNumber(B,Bu),
       bcUnaryLEqReif:unaryLEqReifType(Type),
       bcUnaryLEqReif:unaryLEqReifSimplify(bc(Type,[Au,Bu,Z]), Constr, 1),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_geq_reif(A,B,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcInteger:getUnaryNumber(A,Au),
       bcInteger:getUnaryNumber(B,Bu),
       bcUnaryLEqReif:unaryLEqReifType(Type),
       bcUnaryLEqReif:unaryLEqReifSimplify(bc(Type,[Bu,Au,Z]), Constr, 1),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )   ),
   bParser:addConstraint(Head,Body).

:- Head=int_lt_reif(A,B,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcInteger:getUnaryNumber(A,TAu),
       auxUnarynum:unarynumAddConst(TAu,1,Au),
       bcInteger:getUnaryNumber(B,Bu),
       bcUnaryLEqReif:unaryLEqReifType(Type),
       bcUnaryLEqReif:unaryLEqReifSimplify(bc(Type,[Au,Bu,Z]), Constr, 1),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_gt_reif(A,B,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcInteger:getUnaryNumber(A,Au),
       bcInteger:getUnaryNumber(B,TBu),
       auxUnarynum:unarynumAddConst(TBu,1,Bu),
       bcUnaryLEqReif:unaryLEqReifType(Type),
       bcUnaryLEqReif:unaryLEqReifSimplify(bc(Type,[Bu,Au,Z]), Constr, 1),
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
unaryLEqReifType([
              bcUnaryLEqReif:unaryLEqReifSimplify,
              skipSimplify,
              0,
              bcUnaryLEqReif:unaryLEqReif2cnf,
              unaryLEqReif
             ]).

% --------------------------------
% | Simplify (A <= B)            |
% --------------------------------
unaryLEqReifSimplify(Constr, NewConstr, Changed):-!,
    Constr=bc(Type,[A,B,Z]),
    (ground(Z) ->
        Changed=1,
        bcUnaryLEq:unaryLEqType(LEqType),
        (Z =:= 1 ->
           bcUnaryLEq:unaryLEqSimplify(bc(LEqType,[A,B]), NewConstr, 1)
        ;
           auxUnarynum:unarynumAddConst(B,1,NB),
           bcUnaryLEq:unaryLEqSimplify(bc(LEqType,[NB,A]), NewConstr, 1)
        )
    ;
        auxUnarynum:unarynumIsChangedOrConst(A,NA,Changed),
        auxUnarynum:unarynumIsChangedOrConst(B,NB,Changed),
        (Changed==1 ->
            unaryLEqReif_rangeProp(NA,NB,Z,Type,NewConstr)
        ;
            NewConstr=Constr
        )
    ).



unaryLEqReif_rangeProp((Amin,Amax,Abits,ALbit),(Bmin,Bmax,Bbits,BLbit),Z, Type,Constr):-!,
   (Amax =< Bmin ->
       Constr=none,
       litAsgnTrue(Z) ;
   (Amin > Bmax ->
       Constr=none,
       litAsgnFalse(Z) ;
   (Amin==Amax ->
       Constr=none,
       auxUnarynum:unarynumGEqK((Bmin,Bmax,Bbits,BLbit),Amin,Z) ;
   (Bmin==Bmax ->
       Constr=none,
       Bmin1 is Bmin + 1,
       auxUnarynum:unarynumGEqK((Amin,Amax,Abits,ALbit),Bmin1,-Z) ;
   (Amin == Bmax ->
       %% (A>min or B<max) <-> -Z
       Abits=[Amin1bit|_],
       lit2plit(Amin1bit, X1l,X1op),
       lit2plit(-BLbit,X2l,X2op),
       bcOr:orType(OrType),
       bcOr:orSimplify(bc(OrType,[-Z,(X1l,X1op),(X2l,X2op)]),Constr,_) ;
   Dmin is max(Amin-1,Bmin),
   Dmax is min(Amax,Bmax+1),
   auxUnarynum:unarynumFocusOn((Amin,Amax,Abits,ALbit),Dmin,Dmax,NewA),
   auxUnarynum:unarynumFocusOn((Bmin,Bmax,Bbits,BLbit),Dmin,Dmax,NewB),
   Constr=bc(Type,[NewA,NewB,Z])
   ))))).


% --------------------------------
% | Encode (A <= B) <-> Z        |
% --------------------------------
unaryLEqReif2cnf(bc(_,[A,B,Z]), CnfH-CnfT):-!,
    zIfAleqB(A,B,Z,CnfH-CnfM),
    auxUnarynum:unarynumAddConst(B,1,B1),
    zIfAleqB(B1,A,-Z,CnfM-CnfT).

zIfAleqB(A,B,Z,CnfH-CnfT):-!,
    A=(Amin,_Amax,Abits,_),
    B=(Bmin,_Bmax,Bbits,_),
    (Amin==Bmin ->
        zIfAleqB_(Abits,Bbits,Z,CnfH-CnfT)
    ;
        %% Assert
%        Amin =:= Bmin + 1,!,
        Bbits=[B0|BbitsR],
        CnfH=[[B0,-Z]|CnfM],
        zIfAleqB_(Abits,BbitsR,Z,CnfM-CnfT)
    ).

%%% Z -> A<=B
zIfAleqB_([A|As],[B|Bs],Z,[[-A,B,-Z]|CnfH]-CnfT):-!,
    zIfAleqB_(As,Bs,Z,CnfH-CnfT).
zIfAleqB_([],_,_,Cnf-Cnf):-!.
zIfAleqB_([A|As],[],Z,[[-A,-Z]|CnfH]-CnfT):-!,
    zIfAleqB_(As,[],Z,CnfH-CnfT).