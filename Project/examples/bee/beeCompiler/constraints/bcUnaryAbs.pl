% Author: Amit Metodi
% Last Update: 22/04/2012

:- module(bcUnaryAbs, [ ]).
:- use_module('../auxs/auxLiterals').

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=int_abs(A,B,ConstrsH-ConstrsT),
   Body=(
       !,
       bcInteger:getUnaryNumber(A,Au),
       bcInteger:getUnaryNumber(B,Bu),
       Au=(Amin,Amax,_),
       (Amin >=0 ->
           ConstrsH=ConstrsT,
           auxUnarynum:unarynumEquals(Au,Bu) ;
       (Amax =< 0 ->
           auxUnarynum:unarynumNeg(Au,AuNeg),
           ConstrsH=ConstrsT,
           auxUnarynum:unarynumEquals(AuNeg,Bu) ;
       bcUnaryAbs:splitUnaryNumToPosNeg(Au,AuPos,AuNeg),
       bcUnaryMax:unaryMaxType(Type),
       bcUnaryMax:unaryMaxSimplify(bc(Type,[Bu,AuPos,AuNeg]),Constr,1),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
       ))
   ),
   bParser:addConstraint(Head,Body).
   
   
splitUnaryNumToPosNeg((Amin,Amax,ABits,An),(0,Amax,AposBits,An),(0,AminAbs,AnegBits,-A0)):-!,
   AminAbs is abs(Amin),
   ABits=[A0|_],
   auxLists:listSplit(AminAbs,ABits,AnegBits0,AposBits),
   auxLiterals:litNotReverseXs(AnegBits0,AnegBits).