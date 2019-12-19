% Author: Amit Metodi
% Last Updated: 16/06/2013

:- module(bcUnaryTimesAry, [ ]).

:- Head=int_array_times(Ints,Result,ConstrsH-ConstrsT),
   Body=(!,
         bcUnaryTimesAry:intAryTimesDecompose(Ints,Result,ConstrsH-ConstrsT)
        ),
   bParser:addConstraint(Head,Body).

intAryTimesDecompose([],Res,ConstrsH-ConstrsT):-!,
    bParser:int_eq(0,Res,ConstrsH-ConstrsT).
intAryTimesDecompose([X],Res,ConstrsH-ConstrsT):-!,
    bParser:int_eq(X,Res,ConstrsH-ConstrsT).
intAryTimesDecompose([X,Y],Res,ConstrsH-ConstrsT):-!,
    bParser:int_times(X,Y,Res,ConstrsH-ConstrsT).
intAryTimesDecompose([X,Y|Xs],Res,ConstrsH-ConstrsT):-!,
    bcInteger:getUnaryNumber(X,(Min1,Max1,_)),
    bcInteger:getUnaryNumber(Y,(Min2,Max2,_)),
    Lb is Min1*Min2,Ub is Max1*Max2,
    bParser:new_int(T,Lb,Ub,ConstrsH-Constrs1),
    bParser:int_times(X,Y,T,Constrs1-Constrs2),
    intAryTimesDecompose([T|Xs],Res,Constrs2-ConstrsT).