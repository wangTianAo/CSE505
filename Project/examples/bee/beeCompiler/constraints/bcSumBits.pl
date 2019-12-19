% Author: Amit Metodi
% Last Updated: 18/12/2012


/*
TODO list:
----------
 * Run GCD to reduce coefficients (AdvSimplify)
   if Sum is constant:
      find GCD of {all ai} union {sum} withup to one exception
      consider the case: 2A+4B+5C+6D=8
      GCD=2 and C=0
   if sum isn't constant:
      find GCD of {all ai} and div sum accordingly.
      4A+4B+6C = SUM{1..12} => 2A+2B+3C=SUM'{1..6}
      when SUM must be even.
 
*/


:- module(bcSumBits, [ ]).
:- use_module('../auxs/auxLiterals').
%:- use_module('../auxs/auxUnarynum').
%:- use_module('../auxs/weightBits').

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=bool_array_sum_eq(Bits,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       weightBits:bits2wbits(Bits,WBits),
       bcSumBits:sumBitsType(Type),
       bcInteger:getUnaryNumber(Sum,SumUnary),
       bcSumBits:sumBitsSimplify_step1(bc(Type,[SumUnary|WBits]),Constr,1),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_array_pb_eq(Weights,Bits,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       weightBits:bits2wbits(Bits,Weights,WBits),!,
       weightBits:wbitsToPosWeights(WBits,0,PosWBits,OnesFound),!,
       (OnesFound==0 -> ExBit=(1,-1,1) ; ExBit=(1,1,OnesFound)),
       bcSumBits:sumBitsType(Type),
       bcInteger:getUnaryNumber(Sum,SumUnary),
       bcSumBits:sumBitsSimplify_step1(bc(Type,[SumUnary,ExBit|PosWBits]),Constr,1),
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
sumBitsType([
             bcSumBits:sumBitsSimplify_step1,
             skipSimplify,
             bcSumBits:sumBitsDecompose,
             0,
             sumBits
            ]):-!.

%%% ----- Simplify ----- %%%
sumBitsSimplify_step1(Constr,NewConstr,Changed):-!,
    Constr=bc(Type,[Sum|Bits]),
    weightBits:wbitsUpdate(Bits,0,NBits,OnesFound,Changed),!,
    unarynumIsChanged(Sum,OnesFound,NSum,Changed),!,
    (Changed==1 ->
        (NSum=(0,0,_,_) ->
            NewConstr=none,
            weightBits:wbitsAsgnFalses(NBits) ;
        (NSum=(1,1,_,_) ->
            wbits2plitsW1(NBits,PBits),
            bcExactlyOne:exoType(EXOtype),
            bcExactlyOne:exoSimplify(bc(EXOtype,PBits),NewConstr,_) ;
        (NBits=[] ->
            (NSum=(0,_,SumBits,_) ; throw(unsat)),!,
            NewConstr=none,
            litAsgnFalses(SumBits) ;
        (NBits=[X] ->
            NewConstr=none,
            sum1BitsSimplify(X,NSum) ;
        (NBits=[X1,X2] ->
            sum2BitsSimplify(X1,X2,NSum,NewConstr) ;
        (NSum=(_,Smax,[Sbit],_) ->
            lit2plit(-Sbit,SbitL,SbitOp),
            sumBitsSimplify_step1(bc(Type,[(Smax,Smax,[],1),(SbitL,SbitOp,1)|NBits]),NewConstr,1) ;
        sumBitsSimplify_step2(bc(Type,[NSum|NBits]),NewConstr)
        ))))))
    ;
        NewConstr=Constr
    ).


unarynumIsChanged((Val,Val,_,_),OnesFound,(Val1,Val1,[],1),Changed):-!,
     (OnesFound==0 ->
          Val1 = Val
     ;
          Val1 is Val - OnesFound,
          (Val1 >= 0 ; throw(unsat)),!,
          Changed=1
     ).
unarynumIsChanged(OA,OnesFound,NA,Changed):-
     OA=(Min,Max,[Amn|As],Amx),
     (OnesFound==0 ->
         ((ground(Amn) ; ground(Amx)) ->
             Changed=1,
             auxUnarynum:unarynumFix(OA,NA)
         ;
             NA=OA
         )
     ;
         Changed=1,
         NMin is Min - OnesFound,
         NMax is Max - OnesFound,
         (NMax >= 0 ; throw(unsat)),!,
         (NMin >= 0 ->
             %(NMax >= NMin ; throw(unsat)),!,
             ((ground(Amn) ; ground(Amx)) ->
                  auxUnarynum:unarynumFix((NMin,NMax,[Amn|As],Amx),NA)
             ;
                  NA=(NMin,NMax,[Amn|As],Amx)
             )
         ;
             Ts is abs(NMin),
             auxLists:listSplit(Ts,[Amn|As],Trues,MAbits),!,
             litAsgnTrues(Trues),
             auxUnarynum:unarynumFix((0,NMax,MAbits,Amx),NA)
         )
     ).



sumBitsSimplify_step2(bc(Type,[Sum|WBits]),Constr):-!,
     Sum=(SumLB,SumUB,SumBits,_),
     sumBitsUBsimplify(WBits,SumUB,0,MaxWSum,_ContainEq1,ContainGt1,Changed),!,
     (SumLB > MaxWSum -> throw(unsat) ;
     (Changed==1 ->
          weightBits:wbitsRemoveFalses(WBits,NWBits)
     ;
          NWBits=WBits
     ),!,
     (SumLB == MaxWSum ->
          weightBits:wbitsAsgnTrues(NWBits),
          litAsgnFalses(SumBits),
          Constr=none ;
     (SumUB > MaxWSum ->
          Changed=1,
          auxUnarynum:unarynumSetMax(Sum,MaxWSum,NSum)
     ;
          NSum=Sum
     ),!,
     (ContainGt1 \==1 ; sumBitsLBsimplify(NWBits,MaxWSum,SumLB,Changed)),!,
     (Changed==1 ->
         sumBitsSimplify_step1(bc(Type,[NSum|NWBits]),Constr,_)
     ;
         Constr=bc(Type,[Sum|WBits])
     ))).


sumBitsUBsimplify([(Xl,Xop,Xw)|WBits],SumUB,CurWSum,MaxWSum,ContainEq1,ContainGt1,Changed):-!,
     (Xw =< SumUB ->
        (Xw==1 -> ContainEq1=1 ; ContainGt1=1),
        CurWSum1 is CurWSum + Xw,
        sumBitsUBsimplify(WBits,SumUB,CurWSum1,MaxWSum,ContainEq1,ContainGt1,Changed)
     ;
        Changed=1,
        plitAsgnFalse((Xl,Xop)),
        sumBitsUBsimplify(WBits,SumUB,CurWSum,MaxWSum,ContainEq1,ContainGt1,1)
     ).
sumBitsUBsimplify([],_,MaxWSum,MaxWSum,_,_,_):-!.

sumBitsLBsimplify([(Xl,Xop,Xw)|Xs],MaxWSum,SumLB,Changed):-!,
     (MaxWSum - Xw >= SumLB ; !, plitAsgnTrue((Xl,Xop)), Changed=1),!,
     sumBitsLBsimplify(Xs,MaxWSum,SumLB,Changed).
sumBitsLBsimplify([],_,_,_):-!.


wbits2plitsW1([(Xl,Xop,1)|WBits],[(Xl,Xop)|PBits]):-!,
   wbits2plitsW1(WBits,PBits).
wbits2plitsW1([(Xl,Xop,W)|WBits],PBits):-!,
   W>1,
   plitAsgnFalse((Xl,Xop)),
   wbits2plitsW1(WBits,PBits).
wbits2plitsW1([],[]):-!.


%%% ----- Optimizations ----- %%%
sum1BitsSimplify((Xl,Xop,Xw),(Min,Max,Bits,_)):-
     (Min==0 ->
         (Max >= Xw ->
            auxLists:listSplit(Xw,Bits,Xs,Falses),
            litAsgnFalses(Falses),!,
            unifyXwithYs(Xs,(Xl,Xop))
         ;
            plitAsgnFalse((Xl,Xop)),!,
            litAsgnFalses(Bits)
         )
     ;
         % Min > 0
         ((Max >= Xw, Xw >= Min ) ; throw(unsat)),!,
         plitAsgnTrue((Xl,Xop)),
         Keep is Xw - Min,
         auxLists:listSplit(Keep,Bits,Trues,Falses),!,
         litAsgnTrues(Trues),
         litAsgnFalses(Falses)
     ).

unifyXwithYs([Y|Ys],PX):-!,
     lit2plit(Y,Yl,Yop),
     plitUnify(PX,(Yl,Yop)),
     unifyXwithYs(Ys,PX).
unifyXwithYs([],_):-!.



sum2BitsSimplify(WBit1,WBit2,Sum,Constr):-!,
     bcComparator:comparatorType(CompType),
     createSum2WBitsComparator(WBit1,WBit2,CSum,CompType,Comparator),
     auxUnarynum:unarynumEquals(Sum,CSum),!,
     bcComparator:comparatorSimplify(Comparator, Constr, _).

createSum2WBitsComparator((Xl1,Xop1,Xw1),(Xl2,Xop2,Xw2),Sum,CompType,bc(CompType,[X1,X2,Z1,Z2])):-
    Xw1 =< Xw2,!,
    plit2lit((Xl1,Xop1),X1),
    plit2lit((Xl2,Xop2),X2),
    createListFromBit(Xw1,Z1,FBits-FBits2),
    P is Xw2 - Xw1,
    createListFromBit(P,X2,FBits2-FBits3),
    createListFromBit(Xw1,Z2,FBits3-[]),
    NMax is Xw1 + Xw2,
    Sum = (0,NMax,FBits,Z2).
createSum2WBitsComparator(X1,X2,Sum,CompType,Constr):-!,
    createSum2WBitsComparator(X2,X1,Sum,CompType,Constr).

createListFromBit(0,_,L-L):-!.
createListFromBit(1,X,[X|L]-L):-!.
createListFromBit(I,X,[X,X|LH]-LT):-!,
   I1 is I - 2,
   createListFromBit(I1,X,LH-LT).



:- if(bSettings:sumBitsDecompose(simple)).
%%% ----- Simple Decompose ----- %%%

sumBitsDecompose(bc(_Type,[Sum|WBits]),Constrs):-
     bcComparator:comparatorType(CompType),
     bcUnaryAdder:uadderType(AdderType),
     Sum=(_,Max,_),
     createOddEvenSum(WBits,NSum,Max,AdderType,CompType,Constrs-[]),
     auxUnarynum:unarynumEquals(Sum,NSum).
     
createOddEvenSum([(Xl,Xop,Xw)],(0,Xw,Bits,X),_,_,_,Constrs-Constrs):-!,
     plit2lit((Xl,Xop),X),
     createListFromBit(Xw,X,Bits-[]).
createOddEvenSum([X1,X2],Sum,_Max,_AdderType,CompType,[Constr|Constrs]-Constrs):-!,
     createSum2WBitsComparator(X1,X2,Sum,CompType,Constr).
createOddEvenSum(WBits,Sum,Max,AdderType,CompType,ConstrsH-ConstrsT):-!,
     auxLists:listOddEvenSplit(WBits,WBits1,WBits2),!,
     createOddEvenSum(WBits1,Sum1,Max,AdderType,CompType,ConstrsH-ConstrsM1),!,
     createOddEvenSum(WBits2,Sum2,Max,AdderType,CompType,ConstrsM1-[Constr|ConstrsT]),!,
     Sum1=(0,Max1,_),
     Sum2=(0,Max2,_),
     Max3 is min(Max1 + Max2,Max),
     auxUnarynum:unarynumNewInRange(0,Max3,Sum),
     Constr=bc(AdderType,[Sum1,Sum2,Sum]).
     

:- elif(bSettings:sumBitsDecompose(pairwise)).
%%% ----- Pairwise Decompose ----- %%%
sumBitsDecompose(bc(_Type,[Sum|WBits]),Constrs):-!,
     bcComparator:comparatorType(CompType),
     bcUnaryAdderAgeB:uadderAgeBType(AdderType),
     Sum=(_,Max,_),
     createPairwiseSum(WBits,NSum,Max,AdderType,CompType,Constrs-[]),
     auxUnarynum:unarynumEquals(Sum,NSum).

createPairwiseSum(WBits,Sum,0,_,_,Constrs-Constrs):-!,
     auxUnarynum:unarynumNewInRange(0,0,Sum),
     weightBits:wbitsAsgnFalses(WBits).
createPairwiseSum([(Xl,Xop,Xw)],(0,Xw,Bits,X),_,_,_,Constrs-Constrs):-!,
     plit2lit((Xl,Xop),X),
     createListFromBit(Xw,X,Bits-[]).
createPairwiseSum([X1,X2],Sum,_Max,_AdderType,CompType,[Constr|Constrs]-Constrs):-!,
     createSum2WBitsComparator(X1,X2,Sum,CompType,Constr).
createPairwiseSum(WBits,Sum,Max,AdderType,CompType,ConstrsH-ConstrsT):-!,
     wbitsSplitAgeB_step1(WBits,WBits1,WBits2,[],CompType,ConstrsH-ConstrsM0),!,
     % WBits1 >= WBits2
     createPairwiseSum(WBits1,Sum1,Max,AdderType,CompType,ConstrsM0-ConstrsM1),!,
     UMax2 is Max // 2,
     createPairwiseSum(WBits2,Sum2,UMax2,AdderType,CompType,ConstrsM1-[Constr|ConstrsT]),!,
     Sum1=(0,Max1,_),
     Sum2=(0,Max2,_),
     Max3 is min(Max1 + Max2,Max),
     auxUnarynum:unarynumNewInRange(0,Max3,Sum),
     Constr=bc(AdderType,[Sum1,Sum2,Sum]).

wbitsSplitAgeB_step1([],Os,Es,W1bits,CompType,ConstrsH-ConstrsT):-!,
    wbitsSplitAgeB_step2(W1bits,Os,Es,CompType,ConstrsH-ConstrsT).
wbitsSplitAgeB_step1([(Xl,Xop,Cnt)|More],Os,Es,W1bits,CompType,ConstrsH-ConstrsT):-!,
    (Cnt==1 ->
        wbitsSplitAgeB_step1(More,Os,Es,[(Xl,Xop)|W1bits],CompType,ConstrsH-ConstrsT)
    ;
        Cnt2 is Cnt//2,
        Os=[(Xl,Xop,Cnt2)|MOs],
        Es=[(Xl,Xop,Cnt2)|MEs],
        (Cnt=:=2*Cnt2 ->
            wbitsSplitAgeB_step1(More,MOs,MEs,W1bits,CompType,ConstrsH-ConstrsT)
        ;
            wbitsSplitAgeB_step1(More,MOs,MEs,[(Xl,Xop)|W1bits],CompType,ConstrsH-ConstrsT)
        )
    ).

wbitsSplitAgeB_step2([],[],[],_,Constrs-Constrs):-!.
wbitsSplitAgeB_step2([(Xl,Xop)],[(Xl,Xop,1)],[],_,Constrs-Constrs):-!.
wbitsSplitAgeB_step2([PX,PY|More],[(O,1,1)|Os],[(E,1,1)|Es],CompType,[Comp|ConstrsH]-ConstrsT):-!,
    plit2lit(PX,X),
    plit2lit(PY,Y),
    Comp=bc(CompType,[X,Y,O,E]),
    wbitsSplitAgeB_step2(More,Os,Es,CompType,ConstrsH-ConstrsT).

:- else.

%%% ----- Buckets Decompose ----- %%%

sumBitsDecompose(bc(_Type,[Sum|Bits]),Constrs):-
    weightBits:wbitsToBuckets(Bits,Buckets),
    bcComparator:comparatorType(CompType),
    bcUnaryAdder:uadderType(AdderType),
    Sum=(_,Max,_),
    sumBuckets(Buckets,BSums,Max,AdderType,CompType,Constrs-Constrs2),
    (BSums=[(Weight,BSum)] ->
        Constrs2=[],
        auxUnarynum:unarynumMulByConst((0,BSum),Weight,WSum),
        auxUnarynum:unarynumEquals(Sum,WSum)
    ;
        bcSumUnaries:sumUnariesType(SumType),
        Constrs2=[bc(SumType,[EqTo,FSum|BSums])],
        fixSumToSumInts(Sum,FSum,EqTo)
    ).


fixSumToSumInts((K,K,_,_),(1,1,[1],1),EqTo):-!,
    EqTo is K + 1.
fixSumToSumInts((Min,Max,Bits,_),(1,FMax,[1|FBits],-LBit),EqTo):-!,
    EqTo is Max + 1,
    FMax is Max - Min + 1,
    Bits=[LBit|_],
    litNotReverseXs(Bits,FBits).


createOddEvenSum([X],(0,1,[X],X),_,_,_,Constrs-Constrs):-!.
createOddEvenSum([X1,X2],(0,2,[Y1,Y2],Y2),_Max,_AdderType,CompType,[bc(CompType,[X1,X2,Y1,Y2])|Constrs]-Constrs):-!.
createOddEvenSum(Bits,Sum,Max,AdderType,CompType,ConstrsH-ConstrsT):-!,
    auxLists:listOddEvenSplit(Bits,Bits1,Bits2),!,
    createOddEvenSum(Bits1,Sum1,Max,AdderType,CompType,ConstrsH-ConstrsM1),!,
    createOddEvenSum(Bits2,Sum2,Max,AdderType,CompType,ConstrsM1-[Constr|ConstrsT]),!,
    Sum1=(0,Max1,_),
    Sum2=(0,Max2,_),
    Max3 is min(Max1 + Max2,Max),
    auxUnarynum:unarynumNewInRange(0,Max3,Sum),
    Constr=bc(AdderType,[Sum1,Sum2,Sum]).


sumBuckets([[W|Bucket]|Buckets],[(W,BSum)|BSums],Max,AdderType,CompType,ConstrsH-ConstrsT):-!,
    BMax is Max // W,
    createOddEvenSum(Bucket,(0,BSum),BMax,AdderType,CompType,ConstrsH-ConstrsM),
    sumBuckets(Buckets,BSums,Max,AdderType,CompType,ConstrsM-ConstrsT).
sumBuckets([],[],_,_,_,Constrs-Constrs):-!.

:- endif.