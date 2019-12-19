% Author: Amit Metodi
% Last Updated: 24/07/2016


:- module(bcSumUnaries, [ ]).
:- use_module('../auxs/auxLiterals').
%:- use_module('../auxs/auxUnarynum').
%:- use_module('../auxs/weightUnaries').

/*
TODO:
  * GCD @ advance simplify
  *
*/

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=int_array_plus(Ints,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       (Ints=[] ->
            bcInteger:getUnaryNumber(Sum,SumU),
            auxUnarynum:unarynumEquals(SumU,0),
            ConstrsH=ConstrsT ;
       (Ints=[Int1] ->
            bcInteger:getUnaryNumber(Sum,SumU),
            bcInteger:getUnaryNumber(Int1,Int1U),
            auxUnarynum:unarynumEquals(SumU,Int1U),
            ConstrsH=ConstrsT ;
       (Ints=[Int1,Int2] ->
            bParser:int_plus(Int1,Int2,Sum,ConstrsH-ConstrsT) ;
       weightUnaries:wunariesFix2PosWghtInt([-Sum|Ints],WInts,0,EqTo),
       bcSumUnaries:sumUnariesType(Type),
       bcSumUnaries:sumUnariesSimplify(bc(Type,[EqTo|WInts]),Constr,1),
       (Constr==none ->
            ConstrsH=ConstrsT
       ;
            ConstrsH=[Constr|ConstrsT]
       ))))
   ),
   bParser:addConstraint(Head,Body).

% ----- int_array_sum_rel -----
:- Head=int_array_sum_eq(Ints,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       bParser:int_array_plus(Ints,Sum,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

% ----- int_array_lin_rel -----
:- Head=int_array_lin_eq(Weights,Ints,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       weightUnaries:wunariesFix2PosWghtInt([-1|Weights],[Sum|Ints],WInts,0,EqTo),
       bcSumUnaries:sumUnariesType(Type),
       bcSumUnaries:sumUnariesSimplify(bc(Type,[EqTo|WInts]),Constr,1),
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
sumUnariesType([
             bcSumUnaries:sumUnariesSimplify,
             bcSumUnaries:sumUnariesSimplifyAdv,
             bcSumUnaries:sumUnariesDecompose,
             0,
             sumUnaries
            ]):-!.

%%% ----- Simplify ----- %%%

sumUnariesSimplify(Constr,NewConstr,Changed):-!,
    Constr=bc(Type,[EqTo|WInts]),
    weightUnaries:wunairesUpdate(WInts,0,NWInts,OnesFound,Changed),
    (Changed==1 ->
       NEqTo is EqTo - OnesFound,
       (NEqTo>0 ->
          weightUnaries:wunariesMax(NWInts,0,Max),
          (Max > NEqTo ->
              weightUnaries:wunariesEqTo(NWInts,Max,NEqTo,Changed2),
              (checkSpecialCases(NWInts, NEqTo, NewConstr) ;
                (Changed2==1 ->
                    sumUnariesSimplify(bc(Type,[NEqTo|NWInts]),NewConstr,_)
                ;
                    NewConstr=bc(Type,[NEqTo|NWInts])
                )
              )
          ;
          (Max == NEqTo ->
              weightUnaries:wunariesAsgnMaxs(NWInts),
              NewConstr=none
          ;
              throw(unsat)
          ))
       ;
       (NEqTo==0 ->
          weightUnaries:wunariesAsgnZeros(NWInts),
          NewConstr=none
       ;
       throw(unsat)
       ))
    ;
    NewConstr=Constr
    ).


checkSpecialCases(WInts, EqTo, Constr):-
    (WInts=[Int1] ->
       Int1=(Weight,Int1u),
       auxUnarynum:unarynumMulByConst((0,Int1u),Weight,NSInt),
       auxUnarynum:unarynumEquals(NSInt,EqTo),
       Constr=none ;
    (WInts=[Int1,Int2] ->
       Int1=(Weight1,Int1u),
       auxUnarynum:unarynumMulByConst((0,Int1u),Weight1,NSInt1),
       auxUnarynum:unarynumNeg(NSInt1,NSInt1Neg),
       auxUnarynum:unarynumAddConst(NSInt1Neg,EqTo,Cu),
       Int2=(Weight2,Int2u),
       auxUnarynum:unarynumMulByConst((0,Int2u),Weight2,Au),
       auxUnarynum:unarynumEquals(Au,Cu),
       Constr=none ;
    !,fail
    )).




sumUnariesSimplifyAdv(Constr,NewConstr,Changed):-!,
    Constr=bc(Type,[EqTo|WInts]),
    extractMax1(WInts,RWInts,WBits),
    (RWInts=[] ->
         Changed=1,
         bcSumBits:sumBitsType(SumType),
         bcSumBits:sumBitsSimplify_step1(bc(SumType,[(EqTo,EqTo,[],1)|WBits]),NewConstr,1) ;
    (RWInts=[X] ->
         Changed=1,
         X=(Weight1,Int1u),
         auxUnarynum:unarynumMulByConst((0,Int1u),Weight1,NSInt1),
         auxUnarynum:unarynumNeg(NSInt1,NSInt1Neg),
         auxUnarynum:unarynumAddConst(NSInt1Neg,EqTo,Sum),
         bcSumBits:sumBitsType(SumType),
         bcSumBits:sumBitsSimplify_step1(bc(SumType,[Sum|WBits]),NewConstr,1) ;
    ((WBits=[] ; WBits=[_]) ->
         %%% TODO GCD(WInts)
         NewConstr=Constr ;
    msort(WBits,SWBits),
    simplifyWBits(SWBits,EqTo,FWBits,FEqTo,Changed),
    (Changed==1 ->
       unifyWBits2Ints(FWBits,RWInts,NWInts),
       %%% TODO GCD(NWInts)
       (checkSpecialCases(NWInts, FEqTo, NewConstr) ;
        NewConstr=bc(Type,[FEqTo|NWInts]))
    ;
       %%% TODO GCD(WInts)
       NewConstr=Constr
    )))).

extractMax1([(W,1,_,LBit)|Ints],RInts,[(Xl,Xop,W)|RBits]):-!,
    lit2plit(LBit,Xl,Xop),
    extractMax1(Ints,RInts,RBits).
extractMax1([Int|Ints],[Int|RInts],RBits):-!,
    extractMax1(Ints,RInts,RBits).
extractMax1([],[],[]):-!.

unifyWBits2Ints([(Xl,Xop,W)|WBits],RInts,[(W,1,[X],X)|NInts]):-!,
    plit2lit((Xl,Xop),X),
    unifyWBits2Ints(WBits,RInts,NInts).
unifyWBits2Ints([],RInts,RInts):-!.

simplifyWBits([WB|WBs],EqTo,FWBits,NEqTo,Changed):-!,
    simplifyWBits(WBs,WB,EqTo,FWBits,NEqTo,Changed).
simplifyWBits([],EqTo,[],EqTo,_):-!.
simplifyWBits([X2|WBs],X1,EqTo,FWBits,NEqTo,Changed):-!,
    X1=(X1l,X1op,W1),
    X2=(X2l,X2op,W2),
    (X2l==X1l ->
       Changed=1,
       (X1op==X2op ->
            W is W1 + W2,
            (W =< EqTo ->
               simplifyWBits(WBs,(X1l,X1op,W),EqTo,FWBits,NEqTo,Changed)
            ;
               plitAsgnFalse((X1l,X1op)),
               simplifyWBits(WBs,EqTo,FWBits,NEqTo,Changed)
            )
       ;
            (W1==W2 ->
                EqTo1 is EqTo - W1,
                simplifyWBits(WBs,EqTo1,FWBits,NEqTo,Changed) ;
            (W1 > W2 ->
                W is W1 - W2,
                EqTo1 is EqTo - W2,
                simplifyWBits(WBs,(X1l,X1op,W),EqTo1,FWBits,NEqTo,Changed)
            ;
                W is W2 - W1,
                EqTo1 is EqTo - W1,
                simplifyWBits(WBs,(X2l,X2op,W),EqTo1,FWBits,NEqTo,Changed)
            ))
       )
    ;
       FWBits=[X1|RWBits],
       simplifyWBits(WBs,X2,EqTo,RWBits,NEqTo,Changed)
    ).
simplifyWBits([],X1,EqTo,[X1],EqTo,_):-!.




:- if(bSettings:sumUnariesDecompose(simple)).

%%% ----- Simple Decompose ----- %%%

sumUnariesDecompose(bc(_Type,[EqTo|WInts]),Constrs):-!,
     msort(WInts,SWInts),
     (SWInts=[Int1,Int2,Int3] ->
         Int1=(Weight1,Max1,Bits1,LBit1),
         auxUnarynum:unarynumMulByConst((0,Max1,Bits1,LBit1),Weight1,NSInt1),
         auxUnarynum:unarynumNeg(NSInt1,NSInt1Neg),
         auxUnarynum:unarynumAddConst(NSInt1Neg,EqTo,Cu),
         Int2=(Weight2,Max2,Bits2,LBit2),
         auxUnarynum:unarynumMulByConst((0,Max2,Bits2,LBit2),Weight2,Au),
         Int3=(Weight3,Max3,Bits3,LBit3),
         auxUnarynum:unarynumMulByConst((0,Max3,Bits3,LBit3),Weight3,Bu),
         bcUnaryAdder:uadderType(AdderType),
         Constrs=[bc(AdderType,[Au, Bu, Cu])]
     ;
         extractMax1(SWInts,RWInts,WBits),
         ((WBits=[] ; WBits=[_]) ->
             length(SWInts,IntsCnt),
             createOddEvenSum_eqK(SWInts,IntsCnt,EqTo,Constrs-[])
         ;
             sumWBitsWeights(WBits,0,WBitsMax),
             WBitsUB is min(WBitsMax,EqTo),
             auxUnarynum:unarynumNewInRange(0,WBitsUB,(0,WBsum)),
             bcSumBits:sumBitsType(BitSumType),
             Constrs=[bc(BitSumType,[(0,WBsum),(1,-1,1)|WBits])|ConstrsM],

             length([(1,WBsum)|RWInts],IntsCnt),
             createOddEvenSum_eqK([(1,WBsum)|RWInts],IntsCnt,EqTo,ConstrsM-[])
         )
     ).

sumWBitsWeights([(_,_,W)|WBits],CurMax,TtlMax):-!,
    CurMax1 is CurMax + W,
    sumWBitsWeights(WBits,CurMax1,TtlMax).
sumWBitsWeights([],TtlMax,TtlMax):-!.

createOddEvenSum([(Weight,Max,Bits,LBit)],1,Sum,_,_,Constrs-Constrs):-!,
     auxUnarynum:unarynumMulByConst((0,Max,Bits,LBit),Weight,Sum).
createOddEvenSum(WInts,WIntsCnt,Sum,EqTo,AdderType,ConstrsH-ConstrsT):-!,
     splitIntsList(WInts,WIntsCnt,WInts1,L1,WInts2,L2),
     createOddEvenSum(WInts1,L1,Sum1,EqTo,AdderType,ConstrsH-ConstrsM1),!,
     createOddEvenSum(WInts2,L2,Sum2,EqTo,AdderType,ConstrsM1-[Constr|ConstrsT]),!,
     Sum1=(0,Max1,_),
     Sum2=(0,Max2,_),
     Max3 is min(Max1 + Max2,EqTo),
     auxUnarynum:unarynumNewInRange(0,Max3,Sum),
     Constr=bc(AdderType,[Sum1,Sum2,Sum]).


createOddEvenSum_eqK(WInts,WIntsCnt,EqTo,ConstrsH-ConstrsT):-!,
     bcUnaryAdder:uadderType(AdderType),
     splitIntsList(WInts,WIntsCnt,WInts1,L1,WInts2,L2),
     createOddEvenSum(WInts1,L1,Sum1,EqTo,AdderType,ConstrsH-ConstrsM1),!,
     createOddEvenSum(WInts2,L2,Sum2,EqTo,AdderType,ConstrsM1-[Constr|ConstrsT]),!,

     auxUnarynum:unarynumNeg(Sum1,Sum1Neg),
     auxUnarynum:unarynumAddConst(Sum1Neg,EqTo,Sum1NegEqTo),
     auxUnarynum:unarynumEquals(Sum1NegEqTo,Sum2),!,
     Sum1NegEqTo=(_,_,SumBits,_),
     bcSorted:sortedType(SortedType),
     Constr=bc(SortedType,SumBits).

splitIntsList(WInts,WIntsCnt,WInts1,L1,WInts2,L2):-
     Lt is ceil(WIntsCnt/2),
     ((Lt > 2, Lt mod 2 =:= 1) ->
        L1 is Lt + 1
     ;
        L1 = Lt
     ),
     auxLists:listSplit(L1,WInts,WInts1,WInts2),!,
     L2 is WIntsCnt - L1.


:- else.

%%% ----- Buckets Decompose ----- %%%

sumUnariesDecompose(bc(_Type,[EqTo|WInts]),Constrs):-!,
     msort(WInts,SWInts),
     bcUnaryAdder:uadderType(AdderType),!,
     splitToBuckets(SWInts,InitBuckets),!,
     (InitBuckets=[[BWeight1|BInts1]] ->
         (EqTo mod BWeight1 =:= 0 ->
             EqTo1 is EqTo // BWeight1,
             sumBucket(BInts1,Sum1,EqTo1,AdderType,Constrs-[]),!,
             auxUnarynum:unarynumEquals(Sum1,EqTo1)
         ;
             throw(unsat)
         )
     ;
/*
     (InitBuckets=[[BWeight1|BInts1],[BWeight2|BInts2]] ->
         BMax1 is EqTo // BWeight1,
         BMax2 is EqTo // BWeight2,
         sumBucket(BInts1,Sum1,BMax1,AdderType,Constrs-Constrs1),!,
         sumBucket(BInts2,Sum2,BMax2,AdderType,Constrs1-[]),!,
         auxUnarynum:unarynumMulByConst(Sum1,BWeight1,WSum1),
         auxUnarynum:unarynumNeg(WSum1,WSum1Neg),
         auxUnarynum:unarynumAddConst(WSum1Neg,EqTo,WSum1NegPlus),
         auxUnarynum:unarynumMulByConst(Sum2,BWeight2,WSum2),
         auxUnarynum:unarynumEquals(WSum1NegPlus,WSum2)
     ;
*/
         extractBase2buckets(InitBuckets,1,Base2Buckets,RestBuckets),
         sumBuckets(RestBuckets,EqTo,AdderType,RestSums,Constrs-Constrs1),
         addWIntsToBase2Buckets(RestSums,Base2Buckets,NBase2Buckets),
         sumBuckets(NBase2Buckets,EqTo,AdderType,Base2Sums,Constrs1-Constrs2),
         sumBase2Sums(Base2Sums,EqTo,AdderType,Constrs2-[])
%     )
     ).


sumBucket(WInts,Sum,Max,AdderType,ConstrsH-ConstrsT):-!,
     length(WInts,N),
     sumBucket_(WInts,N,Sum,Max,AdderType,ConstrsH-ConstrsT).

sumBucket_([Int],1,Sum,_,_,Constrs-Constrs):-!,
     Sum=(0,Int).
sumBucket_(WInts,N,Sum,Max,AdderType,ConstrsH-ConstrsT):-!,
     L1 is ceil(N / 2),
     L2 is N - L1,
     auxLists:listSplit(L1,WInts,WInts1,WInts2),!,
     sumBucket_(WInts1,L1,Sum1,Max,AdderType,ConstrsH-ConstrsM),
     sumBucket_(WInts2,L2,Sum2,Max,AdderType,ConstrsM-[Constr|ConstrsT]),
     Sum1=(0,Max1,_),
     Sum2=(0,Max2,_),
     Max3 is min(Max1 + Max2,Max),
     auxUnarynum:unarynumNewInRange(0,Max3,Sum),
     Constr=bc(AdderType,[Sum1,Sum2,Sum]).

specialOddEvenSplit([X1,X2|Xs],[X1|Xs1],[X2|Xs2]):-!,
     specialOddEvenSplit(Xs,Xs2,Xs1).
specialOddEvenSplit([X],[X],[]):-!.
specialOddEvenSplit([],[],[]):-!.

sumBuckets([[Weight|Ints]|Buckets],EqTo,AdderType,[(Weight,Sum)|Sums],ConstrsH-ConstrsT):-!,
    BMax is EqTo // Weight,
    msort(Ints,SInts),
    sumBucket(SInts,Sum,BMax,AdderType,ConstrsH-ConstrsM),
    sumBuckets(Buckets,EqTo,AdderType,Sums,ConstrsM-ConstrsT).
sumBuckets([],_,_,[],Constrs-Constrs):-!.


splitToBuckets([(Weight,Int)|WInts],[[Weight,Int|Bucket]|Buckets]):-!,
     splitToBucket(WInts,Weight,Bucket,RWInts),
     splitToBuckets(RWInts,Buckets).
splitToBuckets([],[]):-!.

splitToBucket([(Weight,Int)|WInts],Weight,[Int|Bucket],RWInts):-!,
     splitToBucket(WInts,Weight,Bucket,RWInts).
splitToBucket(WInts,_,[],WInts):-!.

extractBase2buckets([[Weight|Ints]|Buckets],Weight,[[Weight|Ints]|BucketsB2],BucketsR):-!,
    Weight2 is Weight*2,
    extractBase2buckets(Buckets,Weight2,BucketsB2,BucketsR).
extractBase2buckets([[BWeight|Ints]|Buckets],Weight,BucketsB2,[[BWeight|Ints]|BucketsR]):-
    Weight>BWeight,!,
    extractBase2buckets(Buckets,Weight,BucketsB2,BucketsR).
extractBase2buckets([[BWeight|Ints]|Buckets],Weight,BucketsB2,BucketsR):-
    Weight<BWeight,!,
    Weight2 is Weight*2,
    extractBase2buckets([[BWeight|Ints]|Buckets],Weight2,BucketsB2,BucketsR).
extractBase2buckets([],_,[],[]):-!.



addWIntsToBase2Buckets([],Base2Buckets,Base2Buckets):-!.
addWIntsToBase2Buckets([(Weight,Sum)|WInts],Base2Buckets,NBase2Buckets):-!,
    Sum=(0,Sumu),
    addInt2Buckets(Weight,1,Sumu,Base2Buckets,TBase2Buckets),!,
    addWIntsToBase2Buckets(WInts,TBase2Buckets,NBase2Buckets).
    
    
addInt2Buckets(0,_,_,Base2Buckets,Base2Buckets):-!.
addInt2Buckets(WeightLeft,CurWeight,Sum,Base2Buckets,NBase2Buckets):-
    WeightLeft mod 2 =:= 0,!,
    WeightLeft1 is WeightLeft // 2,
    CurWeight1 is CurWeight * 2,
    addInt2Buckets(WeightLeft1,CurWeight1,Sum,Base2Buckets,NBase2Buckets).
addInt2Buckets(WeightLeft,CurWeight,Sum,Base2Buckets,NBase2Buckets):-!,
    WeightLeft mod 2 =:= 1,!,
    addInt2Buckets_(Base2Buckets,CurWeight,Sum,Base2BucketsRest,NBase2Buckets-NBase2BucketsRest),
    WeightLeft1 is WeightLeft // 2,
    CurWeight1 is CurWeight * 2,
    addInt2Buckets(WeightLeft1,CurWeight1,Sum,Base2BucketsRest,NBase2BucketsRest).

addInt2Buckets_([[LookWeight|Ints]|BucketsRest],LookWeight,Int,BucketsRest,[[LookWeight,Int|Ints]|NBase2Buckets]-NBase2Buckets):-!.
addInt2Buckets_([[CurWeight|Ints]|MoreBuckets],LookWeight,Int,BucketsRest,[[CurWeight|Ints]|NBase2BucketsH]-NBase2BucketsT):-
    LookWeight > CurWeight,!,
    addInt2Buckets_(MoreBuckets,LookWeight,Int,BucketsRest,NBase2BucketsH-NBase2BucketsT).
addInt2Buckets_(BucketsRest,LookWeight,Int,BucketsRest,[[LookWeight,Int]|NBase2Buckets]-NBase2Buckets):-!.


sumBase2Sums(Base2Sums,EqTo,AdderType,ConstrsH-ConstrsT):-
    append(_,[(Base2Max,_)],Base2Sums),
    M is ceil(EqTo / Base2Max),
    NEqTo is M*Base2Max,
    Tare is NEqTo - EqTo,
    addTare(Tare,1,Base2Sums,NBase2Sums),
    NBase2Sums=[(Weight1,Sum1)|RBase2Sums],
    sumBase2Sums_(RBase2Sums,Weight1,Sum1,NEqTo,AdderType,ConstrsH-ConstrsT).


addTare(0,_,Base2Sums,Base2Sums):-!.
addTare(Tare,Weight,Base2Sums,NBase2Sums):-
    Tare2 is Tare // 2,
    Weight2 is Weight*2,
    (Tare mod 2 =:= 1 ->
        addTare_(Base2Sums,Weight,Base2SumsRest,NBase2Sums-NBase2SumsRest),
        addTare(Tare2,Weight2,Base2SumsRest,NBase2SumsRest)
    ;
        addTare(Tare2,Weight2,Base2Sums,NBase2Sums)
    ).


addTare_([(Weight,Sum)|Sums],Weight,Sums,[(Weight,Sum1)|NSums]-NSums):-!,
    auxUnarynum:unarynumAddConst(Sum,1,Sum1).
addTare_([(Weight,Sum)|MoreSums],LookWeight,Sums,[(Weight,Sum)|NSumsH]-NSumsT):-
    LookWeight>Weight,!,
    addTare_(MoreSums,LookWeight,Sums,NSumsH-NSumsT).
addTare_([(Weight,Sum)|Sums],LookWeight,[(Weight,Sum)|Sums],[(LookWeight,(1,1,[],1))|NSums]-NSums):-!.
%%%addTare_([],LookWeight,[],[(LookWeight,(1,1,[],1))|NSums]-NSums):-!.



sumBase2Sums_([(Weight2,Sum2)|Sums],Weight1,Sum1,EqTo,AdderType,ConstrsH-ConstrsT):-
    Weight1<Weight2,!,
    Weight1n is Weight1 * 2,
    EqTo2 is EqTo // 2,
    unarynumEven(Sum1,Sum1n),
    sumBase2Sums_([(Weight2,Sum2)|Sums],Weight1n,Sum1n,EqTo2,AdderType,ConstrsH-ConstrsT).
sumBase2Sums_([(Weight,Sum2)|Sums],Weight,Sum1,EqTo,AdderType,[Constr|ConstrsH]-ConstrsT):-!,
    Sum1=(Min1,Max1,_),
    Sum2=(Min2,Max2,_),
    Max3 is min(EqTo,Max1+Max2),
    Min3 is Min1 + Min2,
    auxUnarynum:unarynumNewInRange(Min3,Max3,Sum3),
    Constr=bc(AdderType,[Sum1,Sum2,Sum3]),
    sumBase2Sums_(Sums,Weight,Sum3,EqTo,AdderType,ConstrsH-ConstrsT).
sumBase2Sums_([],_,Sum1,EqTo,_,Constrs-Constrs):-!,
    auxUnarynum:unarynumEquals(Sum1,EqTo).



unarynumEven((Min,Max,Bits,LBit),(NMin,NMax,NBits,NLBit)):-!,
    (Min mod 2 =:= 0 ->
        unarybitsEven(Bits,NBits,1,NLBit),
        NMin is Min // 2,
        NMax is Max // 2
    ;
        Min1 is Min + 1,
        (Bits=[X|RBits] ->
           litAsgnTrue(X),
           unarynumEven((Min1,Max,RBits,LBit),(NMin,NMax,NBits,NLBit))
        ;
           throw(unsat)
        )
    ).

unarybitsEven([],[], LBit, LBit):-!.
unarybitsEven([X],[], LBit, LBit):-!,
    litAsgnFalse(X).
unarybitsEven([X,Y|Bits],[X|NBits],_,LBit):-!,
    litUnify(X,Y),
    unarybitsEven(Bits,NBits,X,LBit).

:- endif.
