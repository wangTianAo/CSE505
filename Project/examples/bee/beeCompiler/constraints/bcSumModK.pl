% Author: Amit Metodi
% Last Updated: 27/04/2016

:- module(bcSumModK, [ ]).
:- use_module('../auxs/auxLiterals').
:- use_module('../auxs/weightBits').

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=bool_array_sum_modK(Bits,K,SumMod,ConstrsH-ConstrsT),
   Body=(
       !,
       ((integer(K), K>0) ->
           ((K==1 ; Bits=[]) ->
               bcInteger:unifyNumbers(SumMod,0),
               ConstrsH=ConstrsT ;
           (K==2 ->
               bParser:bool2int(SumMod2,SumMod,ConstrsH-ConstrsM),
               bParser:bool_array_xor_reif(Bits,SumMod2,ConstrsM-ConstrsT) ;
           bcInteger:getUnaryNumber(SumMod,SumUnary),
           K1 is K - 1,
           auxUnarynum:unarynumSetMax(SumUnary,K1,SumModKMax),
           auxUnarynum:unarynumSetMin(SumModKMax,0,SumModK),
           weightBits:bits2wbits(Bits,WBits),
           bcSumModK:sumBitsModKType(Type),
           bcSumModK:sumBitsModKSimplify(bc(Type,[SumModK,K,0|WBits]),Constr,1),
           (Constr==none ->
               ConstrsH=ConstrsT
           ;
               ConstrsH=[Constr|ConstrsT]
           )))
       ;
           throw(unsupported(bool_array_sum_modK(boolVars,not(pos_Const),intVar)))
       )
   ),
   bParser:addConstraint(Head,Body).


:- Head=int_array_sum_modK(Ints,K,SumMod,ConstrsH-ConstrsT),
   Body=(
       !,
       ((integer(K), K>0) ->
           ((K==1 ; Ints=[]) ->
               bcInteger:unifyNumbers(SumMod,0),
               ConstrsH=ConstrsT ;
           (Ints=[I1] ->
               bParser:int_mod(I1,K,SumMod,ConstrsH-ConstrsT) ;
           bcInteger:getUnaryNumber(SumMod,SumUnary),
           K1 is K - 1,
           auxUnarynum:unarynumSetMax(SumUnary,K1,SumModKMax),
           auxUnarynum:unarynumSetMin(SumModKMax,0,SumModK),
           (bcSumModK:collectIntUs(Ints,0,IntsU,ConstSum) ->
               bcSumModK:sumIntsModKType(Type),
               bcSumModK:sumIntsModKSimplify(bc(Type,[SumModK,K,ConstSum|IntsU]),Constr,1),
               (Constr==none ->
                   ConstrsH=ConstrsT
               ;
                   ConstrsH=[Constr|ConstrsT]
               )
           ;
               throw(unsupported(int_array_sum_modK(not(pos_Ints),pos_Const,intVar)))
           )))
       ;
           throw(unsupported(int_array_sum_modK(pos_Ints,not(pos_Const),intVar)))
       )
   ),
   bParser:addConstraint(Head,Body).


collectIntUs([Int|Ints],Const,IntUs,ConstSum):-
    bcInteger:getUnaryNumber(Int,IntU),
    IntU=(Min,Max,IntUdata),
    !,Min>=0,!, %% Assert : possitive numbers only
    (Min==Max ->
        NextConst is Const + Min,
        collectIntUs(Ints,NextConst,IntUs,ConstSum) ;
    (Min==0 ->
        IntUs=[IntU|MIntUs],
        collectIntUs(Ints,Const,MIntUs,ConstSum) ;
    NextConst is Const + Min,
    NMax is Max - Min,
    IntUs=[(0,NMax,IntUdata)|MIntUs],
    collectIntUs(Ints,NextConst,MIntUs,ConstSum)
    )).
collectIntUs([],ConstSum,[],ConstSum):-!.

%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
sumBitsModKType([
             bcSumModK:sumBitsModKSimplify,
             skipSimplify,
             bcSumModK:sumBitsModKDecompose,
             0,
             sumBitsModK
            ]):-!.

sumIntsModKType([
             bcSumModK:sumIntsModKSimplify,
             skipSimplify,
             bcSumModK:sumIntsModKDecompose,
             0,
             sumUnariesModK
            ]):-!.

%%% ----- Simplify (Bits) ----- %%%
sumBitsModKSimplify(Constr,NewConstr,Changed):-!,
    Constr=bc(Type,[Sum,K,Ones|Bits]),
    weightBits:wbitsUpdate(Bits,Ones,MBits,NOnes,Changed),!,
    (Changed==1 ->
        OnesModK is NOnes mod K,
        wbitsUpdateModK(MBits,K,OnesModK,NBits,MaxBits), % mod weights
        (NBits=[] ->
            NewConstr=none,
            auxUnarynum:unarynumEquals(Sum,OnesModK) ;
        (NBits=[OneBit] ->
            OneBit=(Xl,Xop,W),
            (Xop == 1 -> X=Xl ; X= -Xl),
            multiplyLit(W,X,XBits),
            Xmax is OnesModK + W,
            (Xmax < K ->
                NewConstr=none,
                auxUnarynum:unarynumEquals(Sum,(OnesModK,Xmax,XBits,X))
            ;
                bcUnaryMod:unaryPosModKType(ModKType),
                bcUnaryMod:modKSimplify_prop((OnesModK,Xmax,XBits,X),K,Sum,ModKType,NewConstr)
            ) ;
        (MaxBits < K ->
            bcSumBits:sumBitsType(SumType),
            (OnesModK > 0 ->
                bcSumBits:sumBitsSimplify_step1(bc(SumType,[Sum,(1,1,OnesModK)|NBits]),NewConstr,_)
            ;
                bcSumBits:sumBitsSimplify_step1(bc(SumType,[Sum|NBits]),NewConstr,_)
            ) ;
        NewConstr=bc(Type,[Sum,K,OnesModK|NBits])
        ))) ;
    NewConstr=Constr
    ).


multiplyLit(W,X,XBits):-
    (W==0 ->
        XBits=[] ;
    W1 is W - 1,
    XBits=[X|MXBits],
    multiplyLit(W1,X,MXBits)).

wbitsUpdateModK([],_,MaxBits,[],MaxBits):-!.
wbitsUpdateModK([B|Bits],K,CurMax,NBits,MaxBits):-
    B=(Xl,Xop,Xw),
    (Xw >= K ->
        XwmodK is Xw mod K,
        (XwmodK > 0 ->
            NBits=[(Xl,Xop,XwmodK)|MBits],
            CurMax1 is CurMax + XwmodK,
            wbitsUpdateModK(Bits,K,CurMax1,MBits,MaxBits)
        ;
            wbitsUpdateModK(Bits,K,CurMax,NBits,MaxBits)
        )
    ;
        NBits=[B|MBits],
        CurMax1 is CurMax + Xw,
        wbitsUpdateModK(Bits,K,CurMax1,MBits,MaxBits)
    ).

%%% ----- Simplify (Ints) ----- %%%
sumIntsModKSimplify(Constr,NewConstr,Changed):-
    Constr=bc(Type,[SumModK,K,Const|Ints]),
    simplifyInts(Ints,Const,NInts,NConst,Changed),
    (Changed==1 ->
        ConstModK is NConst mod K,
        (NInts=[] ->
            auxUnarynum:unarynumEquals(SumModK,ConstModK),
            NewConstr=none ;
        (NInts=[IntU] ->
            auxUnarynum:unarynumAddConst(IntU,ConstModK,IntUplus),
            bcUnaryMod:unaryPosModKType(ModKType),
            bcUnaryMod:modKSimplify_prop(IntUplus,K,SumModK,ModKType,NewConstr) ;
        getSumMaximum(NInts,ConstModK,MaxSum),
        (MaxSum < K ->
            bcSumUnaries:sumUnariesType(SumUsType),
            unaries2wunaries4sum(NInts,WInts),
            sumUnary2wunary4sum(SumModK,ConstModK,SumU,EqTo),
            bcSumUnaries:sumUnariesSimplify(bc(SumUsType,[EqTo,SumU|WInts]),NewConstr,1)
        ;
        NewConstr=bc(Type,[SumModK,K,ConstModK|NInts])
        )))
    ;
        NewConstr=Constr
    ).

simplifyInts([Int|Ints],Const,NInts,NConst,Changed):-!,
    auxUnarynum:unarynumIsChangedOrConst(Int,NInt,IntChanged),!,
    (IntChanged == 1 ->
        Changed=1,
        NInt=(Min,Max,IntData),
        TConst is Const + Min,
        (Max == Min ->
            simplifyInts(Ints,TConst,NInts,NConst,Changed)
        ;
            NMax is Max - Min,
            NInts=[(0,NMax,IntData)|MNInts],
            simplifyInts(Ints,TConst,MNInts,NConst,Changed)
        )
    ;
        NInts=[Int|MNInts],
        simplifyInts(Ints,Const,MNInts,NConst,Changed)
    ).
simplifyInts([],Const,[],Const,_):-!.

getSumMaximum([],Sum,Sum):-!.
getSumMaximum([(_,Max,_)|Ints],CurSum,Sum):-!,
    NextSum is Max + CurSum,
    getSumMaximum(Ints,NextSum,Sum).

unaries2wunaries4sum([(0,Max,Bits,LBit)|Ints],[(1,Max,Bits,LBit)|WInts]):-!,
   unaries2wunaries4sum(Ints,WInts).
unaries2wunaries4sum([],[]):-!.

sumUnary2wunary4sum(SumModK,ConstModK,SumU,EqTo):-
    auxUnarynum:unarynumFix(SumModK,TInt),
    auxUnarynum:unarynumNeg(TInt,(Min,Max,SumData)),
    EqTo is -(ConstModK + Min),
    NMax is Max - Min,
    SumU=(1,NMax,SumData).

%%% ----- Decompose Bits ----- %%%
sumBitsModKDecompose(Constr,Constrs):-!,
    Constr=bc(_Type,[SumMod,K,Ones|Bits]),
    MaxChunkSize is 2*K-2, %%% can be 2*K-1 but prefer even size
    bcSumBits:sumBitsType(SumType),
    sumWeights(Bits,0,SumWeights),
    sumBitChunks(Bits,SumWeights,MaxChunkSize,SumType,ChunkSums,Constrs-ConstrsM),
    bcUnaryMod:unaryPosModKType(ModType),
    bcUnaryAdder:uadderType(AdderType),
    (Ones > 0 ->
        padInts4ModK(Ones,ChunkSums,K,PadChunkSums,RemainOnes),
        decomposeSumModK_top(PadChunkSums,RemainOnes,K,SumMod,AdderType,ModType,ConstrsM)
    ;
        decomposeSumModK_top(ChunkSums,0,K,SumMod,AdderType,ModType,ConstrsM)
    ).

sumWeights([(_,_,W)|Bits],CurSum,TtlSum):-!,
    TSum is CurSum + W,
    sumWeights(Bits,TSum,TtlSum).
sumWeights([],Sum,Sum):-!.

sumBitChunks(Bits,TotalSum,MaxChunkSize,SumType,ChunkSums,ConstrsH-ConstrsT):-!,
    (TotalSum =< MaxChunkSize ->
        auxUnarynum:unarynumNewInRange(0,TotalSum,ChunkSum),
        ChunkSums=[ChunkSum],
        ConstrsH=[bc(SumType,[ChunkSum|Bits])|ConstrsT] ;
    (TotalSum =< 2*MaxChunkSize ->
         HalfSize2 is TotalSum - (TotalSum // 2),
         collectBits2Chunk(Bits,0,HalfSize2,ChunkBits2,ChunkSize2,ChunkBits1),
         ChunkSize1 is TotalSum - ChunkSize2,
         auxUnarynum:unarynumNewInRange(0,ChunkSize1,ChunkSum1),
         auxUnarynum:unarynumNewInRange(0,ChunkSize2,ChunkSum2),
         ChunkSums=[ChunkSum2,ChunkSum1],
         ConstrsH=[bc(SumType,[ChunkSum2|ChunkBits2]),
                   bc(SumType,[ChunkSum1|ChunkBits1])
                   |ConstrsT] ;
    collectBits2Chunk(Bits,0,MaxChunkSize,ChunkBits,ChunkSize,RestBits),
    auxUnarynum:unarynumNewInRange(0,ChunkSize,ChunkSum),
    ChunkSums=[ChunkSum|MChunkSums],
    ConstrsH=[bc(SumType,[ChunkSum|ChunkBits])|ConstrsM],
    NTotalSum is TotalSum - ChunkSize,
    sumBitChunks(RestBits,NTotalSum,MaxChunkSize,SumType,MChunkSums,ConstrsM-ConstrsT)
    )).


collectBits2Chunk([],ChunkSize,_,[],ChunkSize,[]):-!.
collectBits2Chunk(Bits,CurChunkSize,MaxChunkSize,ChunkBits,ChunkSize,RestBits):-
    Bits=[Bit|MBits],!,
    Bit=(_,_,W),
    (CurChunkSize+W =< MaxChunkSize ->
        ChunkBits=[Bit|MChunkBits],
        NextChunkSize is CurChunkSize + W,
        collectBits2Chunk(MBits,NextChunkSize,MaxChunkSize,MChunkBits,ChunkSize,RestBits)
    ;
        ChunkBits=[],
        RestBits=Bits,
        ChunkSize=CurChunkSize
    ).



%%% ----- Decompose Ints ----- %%%
sumIntsModKDecompose(Constr,Constrs):-!,
    Constr=bc(_Type,[SumMod,K,Ones|Ints]),
    bcUnaryMod:unaryPosModKType(ModType),
    (K > 2 ->
        bcUnaryAdder:uadderType(AdderType),
        padInts4ModK(Ones,Ints,K,PaddedInts,RemainOnes),
        decomposeSumModK_top(PaddedInts,RemainOnes,K,SumMod,AdderType,ModType,Constrs)
    ;
        SumMod=(Smin,Smax,_,SLbit),
        ((0 =< Smin , Smax =< 1) ; throw(bug(decompose,sumIntsMod2('bad sum',Smin,Smax)))),
        (Ones==1 ->
            (Smax==1 -> Z=  SLbit ; Z= -1)
        ;
            (Smax==1 -> Z= -SLbit ; Z=  1)
        ),
        decomposeSumIntMod2(Ints,ModType,Bits,Constrs-ConstrsM),
        bcXor:xorType(XorType),
        auxLiterals:lits2plits([Z|Bits],XorVec),
        ConstrsM=[bc(XorType,XorVec)]
    ).

decomposeSumIntMod2([Int|Ints],ModType,Bits,ConstrH-ConstrsT):-!,
    Int=(0,Max,_,LBit),
    (Max==1 ->
        Bits=[LBit|MBits],
        decomposeSumIntMod2(Ints,ModType,MBits,ConstrH-ConstrsT)
    ;
        Bits=[Bit|MBits],
        ConstrH=[bc(ModType,[Int,2,(0,1,[Bit],Bit)])|ConstrM],
        decomposeSumIntMod2(Ints,ModType,MBits,ConstrM-ConstrsT)
    ).
decomposeSumIntMod2([],_,[],Constrs-Constrs):-!.

%%% ----- Decompose Common ----- %%%
padInts4ModK(0,Ints,_,Ints,0):-!.
padInts4ModK(Ones,[Int|Ints],K,PadInts,OnesLeft):-
    Int=(_,Max,_),
    NeedOnes is K -1 - (Max mod K),
    (NeedOnes > 0 ->
        AddOnes is min(NeedOnes,Ones),
        auxUnarynum:unarynumAddConst(Int,AddOnes,PInt),
        PadInts=[PInt|MPadInts],
        NOnes is Ones - AddOnes,
        padInts4ModK(NOnes,Ints,K,MPadInts,OnesLeft)
    ;
        PadInts=[Int|MPadInts],
        padInts4ModK(Ones,Ints,K,MPadInts,OnesLeft)
    ).
padInts4ModK(Ones,[],_,[],Ones):-!.


decomposeSumModK_top(Ints,Ones,K,SumMod,AdderType,ModType,Constrs):-!,
    length(Ints,N),!,
    (N>=2 ->
        N2 is N // 2,
        N1 is N - N2,
        auxLists:listSplit(N1,Ints,Ints1,Ints2),!,
        decomposeSumModK_aux(N1,Ints1,K,SumMod1,AdderType,ModType,Constrs-Constrs1),!,
        decomposeSumModK_aux(N2,Ints2,K,SumMod2,AdderType,ModType,Constrs1-Constrs2),!,
        SumMod1=(_,Max1,_),
        SumMod2=(_,Max2,_),
        Sum3len is Max1+Max2,
        auxUnarynum:unarynumNewInRange(0,Sum3len,Sum3),
        auxUnarynum:unarynumAddConst(Sum3,Ones,Sum3ones),
        Constrs2=[bc(AdderType,[SumMod1,SumMod2,Sum3]),
                  bc(ModType,[Sum3ones,K,SumMod])]
    ;
        Ints=[SingleSum],
        auxUnarynum:unarynumAddConst(SingleSum,Ones,SingleSumOnes),
        Constrs=[bc(ModType,[SingleSumOnes,K,SumMod])]
    ).

decomposeSumModK_aux(1,[Int],K,SumMod,_AdderType,ModType,ConstrsH-ConstrsT):-!,
    Int=(_,Max,_),
    (Max < K ->
        SumMod=Int,
        ConstrsH=ConstrsT
    ;
        K1 is K - 1,
        auxUnarynum:unarynumNewInRange(0,K1,SumMod),
        ConstrsH=[bc(ModType,[Int,K,SumMod])|ConstrsT]
    ).

decomposeSumModK_aux(N,Ints,K,SumMod,AdderType,ModType,ConstrsH-ConstrsT):-!,
    N2 is N // 2,
    N1 is N - N2,
    auxLists:listSplit(N1,Ints,Ints1,Ints2),!,
    decomposeSumModK_aux(N1,Ints1,K,SumMod1,AdderType,ModType,ConstrsH-Constrs1),!,
    decomposeSumModK_aux(N2,Ints2,K,SumMod2,AdderType,ModType,Constrs1-Constrs2),!,
    SumMod1=(_,Max1,_),
    SumMod2=(_,Max2,_),
    Sum3len is Max1+Max2,
    (Sum3len < K ->
        auxUnarynum:unarynumNewInRange(0,Sum3len,SumMod),
        Constrs2=[bc(AdderType,[SumMod1,SumMod2,SumMod])|ConstrsT]
    ;
        auxUnarynum:unarynumNewInRange(0,Sum3len,Sum3),
        K1 is K - 1,
        auxUnarynum:unarynumNewInRange(0,K1,SumMod),
        Constrs2=[bc(AdderType,[SumMod1,SumMod2,Sum3]),
                  bc(ModType,[Sum3,K,SumMod])
                  |ConstrsT]
    ).