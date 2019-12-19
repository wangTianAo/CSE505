% Components: Unary <= Unary
% Author: Amit Metodi
% Last Updated: 01/07/2012

:- module(bcUnaryLEq, [ ]).
:- use_module('../auxs/auxLiterals').
%:- use_module('../auxs/auxLists').

/*
 TODO:
  Advance simplification:
  Support the following rules when X1 >= X2 :
  * Rule 0:
     X1=[A, B,C,D] => B=1
     X2=[E,-B,F,G]
  * Rule 1:
     X1=[ A,B,C,D] => A=1 , G=0
     X2=[-D,E,F,G]
  * Rule 2:
     X1=[D,B,C, A] => D=1
     X2=[G,E,F,-D]
  * Rule 3 (before encoding):
     X1=[A,A,A,A,B,C] =>  [A,A,B,C]
     X2=[D,E,F,G,H,I]     [D,G,H,I]
*/

:- Head=int_leq(A,B,ConstrsH-ConstrsT),
   Body=(
       !,
       bcInteger:getUnaryNumber(A,Au),
       bcInteger:getUnaryNumber(B,Bu),
       bcUnaryLEq:unaryLEqType(Type),
       bcUnaryLEq:unaryLEqSimplify(bc(Type,[Au,Bu]), Constr, 1),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_geq(A,B,ConstrsH-ConstrsT),
   Body=(
       !,
       bcInteger:getUnaryNumber(A,Au),
       bcInteger:getUnaryNumber(B,Bu),
       bcUnaryLEq:unaryLEqType(Type),
       bcUnaryLEq:unaryLEqSimplify(bc(Type,[Bu,Au]), Constr, 1),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).


:- Head=int_lt(A,B,ConstrsH-ConstrsT),
   Body=(
       !,
       bcInteger:getUnaryNumber(A,TAu),
       auxUnarynum:unarynumAddConst(TAu,1,Au),
       bcInteger:getUnaryNumber(B,Bu),
       bcUnaryLEq:unaryLEqType(Type),
       bcUnaryLEq:unaryLEqSimplify(bc(Type,[Au,Bu]), Constr, 1),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_gt(A,B,ConstrsH-ConstrsT),
   Body=(
       !,
       bcInteger:getUnaryNumber(A,Au),
       bcInteger:getUnaryNumber(B,TBu),
       auxUnarynum:unarynumAddConst(TBu,1,Bu),
       bcUnaryLEq:unaryLEqType(Type),
       bcUnaryLEq:unaryLEqSimplify(bc(Type,[Bu,Au]), Constr, 1),
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
unaryLEqType([
              bcUnaryLEq:unaryLEqSimplify,
              skipSimplify,
              0,
              bcUnaryLEq:unaryLEq2cnf,
              unaryLEq
             ]).

% --------------------------------
% | Simplify (A <= B)            |
% --------------------------------
unaryLEqSimplify(Constr, NewConstr, Changed):-!,
    Constr=bc(Type,[A,B]),
    auxUnarynum:unarynumIsChangedOrConst(A,NA,Changed),
    auxUnarynum:unarynumIsChangedOrConst(B,NB,Changed),
    (Changed==1 ->
        unaryLEq_rangeProp(NA,NB,FA,FB,Drop),
        (Drop==1 ->
           NewConstr=none
        ;
           NewConstr=bc(Type,[FA,FB])
        )
    ;
        NewConstr=Constr
    ).

unaryLEq_rangeProp(A,B, NewA, NewB, Drop):-!,
   A=(Amin,Amax,_),
   B=(Bmin,Bmax,_),
   (Amax =< Bmin ->
       Drop=1 ;
   (Amin == Bmax ->
       Drop=1,
       auxUnarynum:unarynumSetMax(A,Bmax,_),
       auxUnarynum:unarynumSetMin(B,Amin,_) ;
   (Amin > Bmax ->
       throw(unsat) ;
   (Amin==Amax ->
       Drop=1,
       auxUnarynum:unarynumSetMin(B,Amin,_) ;
   (Bmin==Bmax ->
       Drop=1,
       auxUnarynum:unarynumSetMax(A,Bmax,_) ;
   Dmin is max(Amin,Bmin),
   Dmax is min(Amax,Bmax),
   getRelevatRange_A(A,Dmin,Dmax,NewA),
   getRelevatRange_B(B,Dmin,Dmax,NewB)
   ))))).

getRelevatRange_A((Amin,Amax,Abits,ALbit),Dmin,Dmax,NA):-
   (Dmin > Amin ->
      Drop is Dmin - Amin,
      auxLists:listDropFrom(Drop,Abits,NAbits),
      (Amax > Dmax ->
          auxUnarynum:unarynumSetMax((Dmin,Amax,NAbits,ALbit),Dmax,NA)
      ;
          NA=(Dmin,Amax,NAbits,ALbit)
      )
   ;
      (Amax > Dmax ->
          auxUnarynum:unarynumSetMax((Amin,Amax,Abits,ALbit),Dmax,NA)
      ;
          NA=(Amin,Amax,Abits,ALbit)
      )
   ).

getRelevatRange_B((Bmin,Bmax,Bbits,BLbit),Dmin,Dmax,NB):-
   (Dmin > Bmin ->
      Drop is Dmin - Bmin,
      auxLists:listSplit(Drop,Bbits,Trues,NBbits),
      litAsgnTrues(Trues),
      (Bmax > Dmax ->
          Keep is Dmax - Dmin,
          keepBits(Keep,NBbits,FBbits,FBLbit),
          NB=(Dmin,Dmax,FBbits,FBLbit)
      ;
          NB=(Dmin,Bmax,NBbits,BLbit)
      )
   ;
      (Bmax > Dmax ->
          Keep is Dmax - Bmin,
          keepBits(Keep,Bbits,FBbits,FBLbit),
          NB=(Bmin,Dmax,FBbits,FBLbit)
      ;
          NB=(Bmin,Bmax,Bbits,BLbit)
      )
   ).

keepBits(1,[B|_],[B],B):-!.
keepBits(2,[B1,B2|_],[B1,B2],B2):-!.
keepBits(3,[B1,B2,B3|_],[B1,B2,B3],B3):-!.
keepBits(4,[B1,B2,B3,B4|_],[B1,B2,B3,B4],B4):-!.
keepBits(5,[B1,B2,B3,B4,B5|_],[B1,B2,B3,B4,B5],B5):-!.
keepBits(I,[B1,B2,B3,B4,B5|Bs],[B1,B2,B3,B4,B5|RBs],FB):-!,
   I1 is I - 5,
   keepBits(I1,Bs,RBs,FB).

% --------------------------------
% | Encoding (A <= B)            |
% --------------------------------
unaryLEq2cnf(bc(_,[A,B]), CnfH-CnfT):-!,
    A=(Xmin,Xmax,Abits,_),
    B=(Xmin,Xmax,Bbits,_),
    xiDragYi(Abits,Bbits,CnfH-CnfT).

xiDragYi([A|As],[B|Bs],[[-A,B]|CnfH]-CnfT):-!,
    xiDragYi(As,Bs,CnfH-CnfT).
xiDragYi([],[],Cnf-Cnf):-!.