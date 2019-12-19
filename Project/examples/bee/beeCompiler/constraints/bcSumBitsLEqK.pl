% Author: Amit Metodi
% Last Updated: 30/08/2016

/*
%%% constraint is
%%% a1*x1 + ... + an*xn <= SumUB
%%%%% =>
%%%%% a1*(-x1) + ... + an*(-xn) >= SumLB
%%%%% When SumUB = sum(ai) - SumLB

TODO list:
----------
 * Run GCD to reduce coefficients if possible
 * better encoding for the case where coefficients values > 1
*/


:- module(bcSumBitsLEqK, [ ]).
:- use_module('../auxs/auxLiterals').
%:- use_module('../auxs/auxUnarynum').
%:- use_module('../auxs/weightBits').

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=bool_array_sum_leq(Bits,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       length(Bits,BCnt),
       auxLists:listListOf(BCnt,1,Weights),!,
       bParser:bool_array_pb_leq(Weights,Bits,Sum,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_array_sum_lt(Bits,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       length(Bits,BCnt),
       auxLists:listListOf(BCnt,1,Weights),!,
       bParser:bool_array_pb_leq([1|Weights],[1|Bits],Sum,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_array_sum_gt(Bits,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       length(Bits,BCnt),
       auxLists:listListOf(BCnt,-1,Weights),!,
       bParser:bool_array_pb_leq([1|Weights],[1|Bits],-Sum,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).


:- Head=bool_array_sum_geq(Bits,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       length(Bits,BCnt),
       auxLists:listListOf(BCnt,-1,Weights),!,
       bParser:bool_array_pb_leq(Weights,Bits,-Sum,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).


:- Head=bool_array_pb_leq(Weights,Bits,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       bcInteger:getUnaryNumber(Sum,SumUnary),
       (SumUnary=(K,K,_,_) ->
           weightBits:bits2wbits(Bits,Weights,WBits),!,
           weightBits:wbitsToPosWeights(WBits,PosWBits),!,
           bcSumBitsLEqK:sumBitsLEqKType(Type),
           bcSumBitsLEqK:sumBitsLEqKSimplify_step1(bc(Type,[K|PosWBits]),Constr,1),
           (Constr==none ->
               ConstrsH=ConstrsT
           ;
               ConstrsH=[Constr|ConstrsT]
           ) ;
       ((SumUnary=(LB,UB,_,LBit), LB+1=:=UB) ->
           weightBits:bits2wbits([-LBit|Bits],[1|Weights],WBits),!,
           weightBits:wbitsToPosWeights(WBits,PosWBits),!,
           bcSumBitsLEqK:sumBitsLEqKType(Type),
           bcSumBitsLEqK:sumBitsLEqKSimplify_step1(bc(Type,[UB|PosWBits]),Constr,1),
           (Constr==none ->
               ConstrsH=ConstrsT
           ;
               ConstrsH=[Constr|ConstrsT]
           ) ;
       %% Decompose constraint
       SumUnary=(_,UB,_,_),
       bcSumBitsLEqK:sumWeightLB(Weights,0,LB),!,
       bParser:new_int(NewSum,LB,UB,ConstrsH-Constrs1),!,
       bParser:bool_array_pb_eq(Weights,Bits,NewSum,Constrs1-Constrs2),!,
       bParser:int_leq(NewSum,Sum,Constrs2-ConstrsT)
       ))
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_array_pb_lt(Weights,Bits,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       bParser:bool_array_pb_leq([1|Weights],[1|Bits],Sum,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_array_pb_gt(Weights,Bits,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       bcSumBitsLEqK:negWeights(Weights,NWeights),!,
       bParser:bool_array_pb_leq([1|NWeights],[1|Bits],-Sum,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_array_pb_geq(Weights,Bits,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       bcSumBitsLEqK:negWeights(Weights,NWeights),!,
       bParser:bool_array_pb_leq(NWeights,Bits,-Sum,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).


negWeights([X|Xs],[Y|Ys]):-!,
    Y is -X,
    negWeights(Xs,Ys).
negWeights([],[]):-!.


sumWeightLB([W|Ws],Cur,LB):-!,
    (W < 0 ->
        Cur1 is Cur + W,
        sumWeightLB(Ws,Cur1,LB)
    ;
        sumWeightLB(Ws,Cur,LB)
    ).
sumWeightLB([],LB,LB):-!.


%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
sumBitsLEqKType([
             bcSumBitsLEqK:sumBitsLEqKSimplify_step1,
             skipSimplify,
             bcSumBitsLEqK:sumBitsLEqKDecompose,
             0,
             sumBitsLEqK
            ]):-!.

%%% ----- Simplify ----- %%%
sumBitsLEqKSimplify_step1(Constr,NewConstr,Changed):-!,
    Constr=bc(Type,[SumUB|Bits]),
    weightBits:wbitsUpdate(Bits,0,NBits,OnesFound,Changed),!,
    (Changed==1 ->
        NSumUB is SumUB - OnesFound,
        (NSumUB >= 1 ->
            sumBitsLEqKSimplify_step2(bc(Type,[NSumUB|NBits]),NewConstr) ;
        (NSumUB == 0 ->
            NewConstr=none,
            weightBits:wbitsAsgnFalses(NBits) ;
        throw(unsat)
        ))
    ;
        NewConstr=Constr
    ).

sumBitsLEqKSimplify_step2(Constr,NewConstr):-!,
     Constr=bc(Type,[SumUB|WBits]),
     bcSumBits:sumBitsUBsimplify(WBits,SumUB,0,MaxWSum,_ContainEq1,ContainGt1,Changed),!,
     (MaxWSum =< SumUB -> NewConstr=none ;
     (Changed==1 ->
          weightBits:wbitsRemoveFalses(WBits,NWBits)
     ;
          NWBits=WBits
     ),!,
     (SumUB == 1 ->
         Changed=1,
         removeWeightFromBits(NWBits,Vec),
         bcAtMostOne:amoType(AMOtype),
         bcAtMostOne:amoSimplify(bc(AMOtype,Vec),NewConstr,_) ;
     SumLB is MaxWSum - SumUB,  %% SumLB > 0
     (SumLB == 1 ->
         removeWeightFromBitsNNeg(NWBits,Vec),
         bcAtLeastOne:aloType(ALOtype),
         bcAtLeastOne:aloSimplify(bc(ALOtype,Vec),NewConstr,_) ;
     (ContainGt1 \==1 ; sumBitsLBsimplifyF(NWBits,MaxWSum,SumLB,Changed)),!,
     (Changed==1 ->
         sumBitsLEqKSimplify_step1(bc(Type,[SumUB|NWBits]),NewConstr,_)
     ;
         NewConstr=Constr
     )))).


sumBitsLBsimplifyF([(Xl,Xop,Xw)|Xs],MaxWSum,SumLB,Changed):-!,
     (MaxWSum - Xw >= SumLB ; !, plitAsgnFalse((Xl,Xop)), Changed=1),!,
     sumBitsLBsimplifyF(Xs,MaxWSum,SumLB,Changed).
sumBitsLBsimplifyF([],_,_,_):-!.

removeWeightFromBits([(Xl,Xop,_)|WXs],[(Xl,Xop)|Xs]):-!,
     removeWeightFromBits(WXs,Xs).
removeWeightFromBits([],[]):-!.

removeWeightFromBitsNNeg([(Xl,Xop,_)|WXs],[(Xl,NXop)|Xs]):-!,
     NXop is -(Xop),
     removeWeightFromBitsNNeg(WXs,Xs).
removeWeightFromBitsNNeg([],[]):-!.


:- if(bSettings:sumBitsDecompose(simple)).

%%% ----- Simple Decompose ----- %%%

sumBitsLEqKDecompose(bc(_Type,[K|WBits]),Constrs):-
    bcComparator:comparatorType(CompType),
    bcUnaryAdder:uadderType(AdderType),

    auxLists:listOddEvenSplit(WBits,WBits1,WBits2),!,
    bcSumBits:createOddEvenSum(WBits1,Sum1,K,AdderType,CompType,Constrs-ConstrsM),!,
    bcSumBits:createOddEvenSum(WBits2,Sum2,K,AdderType,CompType,ConstrsM-[Constr]),!,

    auxUnarynum:unarynumNeg(Sum2,Sum2Neg),
    auxUnarynum:unarynumAddConst(Sum2Neg,K,(S2Min,S2Max,S2Bits,S2Lbit)),

    bcUnaryLEq:unaryLEqType(LEqType),
    S2MinF is S2Min - 1,
    Constr=bc(LEqType,[Sum1,(S2MinF,S2Max,[1|S2Bits],S2Lbit)]).
    
:- elif(bSettings:sumBitsDecompose(pairwise)).
%%% ----- Pairwise Decompose ----- %%%

sumBitsLEqKDecompose(bc(_Type,[K|WBits]),Constrs):-
    bcComparator:comparatorType(CompType),
    bcUnaryAdderAgeB:uadderAgeBType(AdderType),
    bcSumBits:createPairwiseSum(WBits,_Sum,K,AdderType,CompType,Constrs-[]).

:- else.

%%% ----- Buckets Decompose ----- %%%

sumBitsLEqKDecompose(bc(_Type,[K|Bits]),Constrs):-
    weightBits:wbitsToBuckets(Bits,Buckets),
    bcComparator:comparatorType(CompType),
    bcUnaryAdder:uadderType(AdderType),
    bSumBits:sumBuckets(Buckets,BSums,K,AdderType,CompType,Constrs-Constrs2),
    (BSums=[(Weight,BSum)] ->
        Constrs2=[],
        auxUnarynum:unarynumMulByConst((0,BSum),Weight,WSum),
        auxUnarynum:unarynumSetMax(WSum,K)
    ;
        bcSumUnariesLEqK:sumUnariesLEqKType(SumType),
        Constrs2=[bc(SumType,[K|BSums])]
    ).

:- endif.