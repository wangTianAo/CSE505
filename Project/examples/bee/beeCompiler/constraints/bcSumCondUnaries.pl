% Author: Amit Metodi
% Last Updated: 20/05/2017


:- module(bcSumCondUnaries, [ ]).
:- use_module('../auxs/auxLiterals').

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=int_array_sumCond_eq(Bools,Ints,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       bcSumCondUnaries:condInts2PosWghtInts([1|Bools],[-Sum|Ints],0,WInts,EqTo,ConstrsH-ConstrsM),
       bcSumUnaries:sumUnariesType(Type),
       bcSumUnaries:sumUnariesSimplify(bc(Type,[EqTo|WInts]),Constr,1),
       (Constr==none ->
            ConstrsM=ConstrsT
       ;
            ConstrsM=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_array_sumCond_leq(Bools,Ints,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       bcSumCondUnaries:condInts2PosWghtInts([1|Bools],[-Sum|Ints],0,WInts,LEqTo,ConstrsH-ConstrsM),
       bcSumUnariesLEqK:sumUnariesLEqKType(Type),
       bcSumUnariesLEqK:sumUnariesLEqKSimplify(bc(Type,[LEqTo|WInts]),Constr,1),
       (Constr==none ->
            ConstrsM=ConstrsT
       ;
            ConstrsM=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_array_sumCond_lt(Bools,Ints,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       bcSumCondUnaries:condInts2PosWghtInts([1|Bools],[-Sum|Ints],-1,WInts,LEqTo,ConstrsH-ConstrsM),
       bcSumUnariesLEqK:sumUnariesLEqKType(Type),
       bcSumUnariesLEqK:sumUnariesLEqKSimplify(bc(Type,[LEqTo|WInts]),Constr,1),
       (Constr==none ->
            ConstrsM=ConstrsT
       ;
            ConstrsM=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).
   
:- Head=int_array_sumCond_geq(Bools,Ints,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       bcSumUnariesLEqK:negInts(Ints,NInts),
       bParser:int_array_sumCond_leq(Bools,NInts,-Sum,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_array_sumCond_gt(Bools,Ints,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       bcSumUnariesLEqK:negInts(Ints,NInts),
       bParser:int_array_sumCond_lt(Bools,NInts,-Sum,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).
   
   
%%% ------------------------- %%%
%%%          Auxilary         %%%
%%% ------------------------- %%%
condInts2PosWghtInts([B|Bs],[U|Us],CurEqTo,WUs,EqTo,ConstrsH-ConstrsT):-!,
    (ground(B) ->
        (B =:= -1 ->
            condInts2PosWghtInts(Bs,Us,CurEqTo,WUs,EqTo,ConstrsH-ConstrsT)
        ;
            bcInteger:getUnaryNumber(U,Uint),
            Uint=(Min,Max,UBits,LUBit),
            NMax is Max - Min,
            UpdEqTo is CurEqTo - Min,
            WUs=[(1,NMax,UBits,LUBit)|MWUs],
            condInts2PosWghtInts(Bs,Us,UpdEqTo,MWUs,EqTo,ConstrsH-ConstrsT)
        )
    ;
    bcInteger:getUnaryNumber(U,Uint),
    Uint=(Min,Max,_),
    (Min==Max ->
        (Min == 0 ->
            condInts2PosWghtInts(Bs,Us,CurEqTo,WUs,EqTo,ConstrsH-ConstrsT) ;
        (Min > 0 ->
            WUs=[(Min,1,[B],B)|MWUs],
            condInts2PosWghtInts(Bs,Us,CurEqTo,MWUs,EqTo,ConstrsH-ConstrsT)
        ;
            NegMin is -Min,
            WUs=[(NegMin,1,[-B],-B)|MWUs],
            UpdEqTo is CurEqTo - Min,
            condInts2PosWghtInts(Bs,Us,UpdEqTo,MWUs,EqTo,ConstrsH-ConstrsT)
        ))
    ;
        NMax is Max - Min,
        UpdEqTo is CurEqTo - Min,
        
        auxUnarynum:unarynumNewInRange(Min,Max, BU),
        BU = (Min,Max,CBits,LCBit),
        bcSorted:sortedType(SortType),
        SortConstr=bc(SortType,CBits),

        bcUnaryTimes:utimesType(MulType),!,
        bcUnaryTimes:utimesSimplify(bc(MulType,[Uint, (0,1,[B],B), BU]), MulConstr, 1),
        (MulConstr==none ->
            ConstrsH=[SortConstr|ConstrsM]
        ;
            ConstrsH=[SortConstr,MulConstr|ConstrsM]
        ),
        WUs=[(1,NMax,CBits,LCBit)|MWUs],
        condInts2PosWghtInts(Bs,Us,UpdEqTo,MWUs,EqTo,ConstrsM-ConstrsT)
    )).
condInts2PosWghtInts([],[],EqTo,[],EqTo,Constrs-Constrs):-!.
