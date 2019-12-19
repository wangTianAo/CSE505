% Authors: Amit Metodi
% Last Updated: 23/04/2016

:- module(bcSumModDivK, [ ]).

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%

:- Head=bool_array_sum_modK_old(Bits,K,SumMod,ConstrsH-ConstrsT),
   Body=(
       !,
       ((integer(K), K>0) ->
           ((K==1 ; Bits=[]) ->
               bcInteger:unifyNumbers(SumMod,0),
               ConstrsH=ConstrsT ;
           (K==2 ->
               bParser:bool2int(SumMod2,SumMod,ConstrsH-ConstrsM),
               bParser:bool_array_xor_reif(Bits,SumMod2,ConstrsM-ConstrsT) ;
           bcSumModDivK:decomposeSumBitsModK(Bits,K,SumMod,ConstrsH-ConstrsT)
           ))
       ;
           throw(unsupported(bool_array_sum_modK(boolVars,not(posConst),intVar)))
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_array_sum_divModK(Bits,K,SumDiv,SumMod,ConstrsH-ConstrsT),
   Body=(
       !,
       ((integer(K), K>0) ->
           (K=:=1 ->
               bcInteger:unifyNumbers(SumMod,0),
               bParser:bool_array_sum_eq(Bits,SumDiv,ConstrsH-ConstrsT)
           ;
               bcSumModDivK:decomposeSumBitsDivModK(Bits,K,SumDiv,SumMod,ConstrsH-ConstrsT)
           )
       ;
           throw(unsupported(bool_array_sum_divModK(boolVars,not(posConst),intVar,intVar)))
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_array_sum_divK(Bits,K,SumDiv,ConstrsH-ConstrsT),
   Body=(
       !,
       ((integer(K), K>0) ->
           (K=:=1 ->
               bParser:bool_array_sum_eq(Bits,SumDiv,ConstrsH-ConstrsT)
           ;
               bcSumModDivK:decomposeSumBitsDivK(Bits,K,SumDiv,ConstrsH-ConstrsT)
           )
       ;
           throw(unsupported(bool_array_sum_divK(boolVars,not(posConst),intVar)))
       )
   ),
   bParser:addConstraint(Head,Body).
   
:- Head=int_array_sum_modK_old(Ints,K,SumMod,ConstrsH-ConstrsT),
   Body=(
       !,
       ((integer(K), K>0) ->
           ((K=:=1 ; Ints=[]) ->
               bcInteger:unifyNumbers(SumMod,0),
               ConstrsH=ConstrsT ;
           (Ints=[I1] ->
               bParser:int_mod(I1,K,SumMod,ConstrsH-ConstrsT) ;
           bcSumModDivK:decomposeSumModK(Ints,K,SumMod,ConstrsH-ConstrsT)
           ))
       ;
           throw(unsupported(int_array_sum_modK(intVars,not(posConst),intVar)))
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_array_sum_divModK(Ints,K,SumDiv,SumMod,ConstrsH-ConstrsT),
   Body=(
       !,
       ((integer(K), K>0) ->
           (K=:=1 ->
               bcInteger:unifyNumbers(SumMod,0),
               bParser:bParser:int_array_plus(Ints,SumDiv,ConstrsH-ConstrsT) ;
           (Ints=[] ->
               bcInteger:unifyNumbers(SumDiv,0),
               bcInteger:unifyNumbers(SumMod,0),
               ConstrsH=ConstrsT ;
           (Ints=[I1] ->
               bParser:int_mod(I1,K,SumMod,ConstrsH-ConstrsM),
               bParser:int_div(I1,K,SumDiv,ConstrsM-ConstrsT) ;
           bcSumModDivK:decomposeSumDivModK(Ints,K,SumDiv,SumMod,ConstrsH-ConstrsT)
           )))
       ;
           throw(unsupported(int_array_sum_divModK(intVars,not(posConst),intVar,intVar)))
       )
   ),
   bParser:addConstraint(Head,Body).
   

:- Head=int_array_sum_divK(Ints,K,SumDiv,ConstrsH-ConstrsT),
   Body=(
       !,
       ((integer(K), K>0) ->
           (K=:=1 ->
               bParser:bParser:int_array_plus(Ints,SumDiv,ConstrsH-ConstrsT) ;
           (Ints=[] ->
               bcInteger:unifyNumbers(SumDiv,0),
               ConstrsH=ConstrsT ;
           (Ints=[I1] ->
               bParser:int_div(I1,K,SumDiv,ConstrsH-ConstrsT) ;
           bcSumModDivK:decomposeSumDivK(Ints,K,SumDiv,ConstrsH-ConstrsT)
           )))
       ;
           throw(unsupported(int_array_sum_divModK(intVars,not(posConst),intVar,intVar)))
       )
   ),
   bParser:addConstraint(Head,Body).

%%% ------------------------- %%%
%%% decompoosition            %%%
%%% ------------------------- %%%

%% ---------- BITS ---------- %%
decomposeSumBitsModK(Bits,K,SumMod,ConstrsH-ConstrsT):-!,
    length(Bits,N),
    bcSumBits:sumBitsType(SumType),
    decomposeSumBitsDivModK_aux(Bits,N,K,SumModT,SumType,_,ConstrsH-ConstrsT),!,
    % mod
    bcInteger:getUnaryNumber(SumMod,SumModU),
    auxUnarynum:unarynumEquals(SumModU,SumModT).

decomposeSumBitsDivModK(Bits,K,SumDiv,SumMod,ConstrsH-ConstrsT):-!,
    length(Bits,N),
    bcSumBits:sumBitsType(SumType),
    decomposeSumBitsDivModK_aux(Bits,N,K,SumModT,SumType,SumDivBits-[],ConstrsH-Cs1),!,
    % mod
    bcInteger:getUnaryNumber(SumMod,SumModU),
    auxUnarynum:unarynumEquals(SumModU,SumModT),!,
    % div
    MaxDiv is (N + K - 1) // K,
    bcInteger:getUnaryNumber(SumDiv,SumDivU),
    auxUnarynum:unarynumSetMax(SumDivU,MaxDiv,_),
    bParser:bool_array_sum_eq(SumDivBits,SumDiv,Cs1-ConstrsT).
                
decomposeSumBitsDivK(Bits,K,SumDiv,ConstrsH-ConstrsT):-!,
    length(Bits,N),
    bcSumBits:sumBitsType(SumType),
    decomposeSumBitsDivModK_aux(Bits,N,K,_SumModT,SumType,SumDivBits-[],ConstrsH-Cs1),!,
    % div
    MaxDiv is (N + K - 1) // K,
    bcInteger:getUnaryNumber(SumDiv,SumDivU),
    auxUnarynum:unarynumSetMax(SumDivU,MaxDiv,_),
    bParser:bool_array_sum_eq(SumDivBits,SumDiv,Cs1-ConstrsT).
        
decomposeSumBitsDivModK_aux(Bits,N,K,SumMod,SumType,SumDivBits-SumDivBits,ConstrsH-ConstrsT):-
    N < K,!,% base case
    auxUnarynum:unarynumNewInRange(0,N,SumMod),
    weightBits:bits2wbits(Bits,WBits),
    bcSumBits:sumBitsSimplify_step1(bc(SumType,[SumMod|WBits]),Constr,1),
    (Constr==none ->
        ConstrsH=ConstrsT
    ;
        ConstrsH=[Constr|ConstrsT]
    ).

decomposeSumBitsDivModK_aux(Bits,N,K,SumMod,SumType,SumDivBitsH-SumDivBitsT,ConstrsH-ConstrsT):-
    N2 is N // 2,
    N1 is N - N2,!,
    auxLists:listSplit(N1,Bits,Bits1,Bits2),
    decomposeSumBitsDivModK_aux(Bits1,N1,K,SumMod1,SumType,SumDivBitsH-SumDivBits1,ConstrsH-Constrs1),
    decomposeSumBitsDivModK_aux(Bits2,N2,K,SumMod2,SumType,SumDivBits1-SumDivBits2,Constrs1-Constrs2),
    Sum3len is min(N1,K-1)+min(N2,K-1),
    auxUnarynum:unarynumNewInRange(0,Sum3len,SumMod3),
    auxUnarynum:unarynumGEqK(SumMod3,K,Sum3bit),
    SumDivBits2=[Sum3bit|SumDivBitsT],
    bcUnaryAdder:uadderSimplify1st(bc(_,[SumMod1, SumMod2, SumMod3]), Constr, _),
    (Constr==none ->
        Constrs2=Constrs3
    ;
        Constrs2=[Constr|Constrs3]
    ),
    specialCaseMod(SumMod3,K,SumMod,Constrs3-ConstrsT).


%% ---------- INTS ---------- %%

decomposeSumModK(Ints,K,SumMod,ConstrsH-ConstrsT):-!,
   fixInts_mod(Ints,K,ModInts,ConstrsH-Cs1),
   (K==2 ->
       extractMod2Bits(ModInts,Bits),
       bcInteger:getUnaryNumber(SumMod,SumModU),
       auxUnarynum:unarynumEquals(SumModU,(0,1,[SumBit],SumBit)),
       bParser:bool_array_xor_reif(Bits,SumBit,Cs1-ConstrsT)
   ;
       length(ModInts,N),
       decomposeSumModDivK_aux(ModInts,N,K,SumModT,_,Cs1-ConstrsT),!,
       % mod
       bcInteger:getUnaryNumber(SumMod,SumModU),
       auxUnarynum:unarynumEquals(SumModU,SumModT)
   ).

extractMod2Bits([Int|Ints],[Bit|Bits]):-!,
    bcInteger:getUnaryNumber(Int,IntU),
    auxUnarynum:unarynumGEqK(IntU,1,Bit),
    extractMod2Bits(Ints,Bits).
extractMod2Bits([],[]):-!.


decomposeSumDivModK(Ints,K,SumDiv,SumMod,ConstrsH-ConstrsT):-!,
   fixInts_divmod(Ints,K,ModInts,DivInts,ConstrsH-Cs1),
   length(ModInts,N),
   decomposeSumModDivK_aux(ModInts,N,K,SumModT,SumDivBits-[],Cs1-Cs2),!,
   % mod
   bcInteger:getUnaryNumber(SumMod,SumModU),
   auxUnarynum:unarynumEquals(SumModU,SumModT),!,
   % div
   (DivInts == [] ->
       bParser:bool_array_sum_eq(SumDivBits,SumDiv,Cs2-ConstrsT)
   ;
       length(SumDivBits,NBits),
       bParser:new_int(SumBits,0,NBits,Cs2-Cs3),
       bParser:bool_array_sum_eq(SumDivBits,SumBits,Cs3-Cs4),
       bParser:int_array_sum_eq([SumBits|DivInts],SumDiv,Cs4-ConstrsT)
   ).

decomposeSumDivK(Ints,K,SumDiv,ConstrsH-ConstrsT):-!,
   fixInts_divmod(Ints,K,ModInts,DivInts,ConstrsH-Cs1),
   length(ModInts,N),
   decomposeSumModDivK_aux(ModInts,N,K,_SumModT,SumDivBits-[],Cs1-Cs2),!,
   % div
   (DivInts == [] ->
       bParser:bool_array_sum_eq(SumDivBits,SumDiv,Cs2-ConstrsT)
   ;
       length(SumDivBits,NBits),
       bParser:new_int(SumBits,0,NBits,Cs2-Cs3),
       bParser:bool_array_sum_eq(SumDivBits,SumBits,Cs3-Cs4),
       bParser:int_array_sum_eq([SumBits|DivInts],SumDiv,Cs4-ConstrsT)
   ).

fixInts_divmod([Int|Ints],K,ModInts,DivInts,CsH-CsT):-
    bcInteger:getUnaryNumber(Int,IntU),
    IntU=(Min,Max,_),
    %% Assert : possitive numbers only
    !,Min >= 0,!,
    (Max < K ->
        ModInts=[Int|MModInts],
        fixInts_divmod(Ints,K,MModInts,DivInts,CsH-CsT)
    ;
        K1 is K -1,
        bParser:new_int(ModInt,0,K1,CsH-Cs1),
        bParser:int_mod(Int,K,ModInt,Cs1-Cs2),
        K2 is Max // K,
        bParser:new_int(DivInt,0,K2,Cs2-Cs3),
        bParser:int_div(Int,K,DivInt,Cs3-Cs4),
        ModInts=[ModInt|MModInts],
        DivInts=[DivInt|MDivInts],
        fixInts_divmod(Ints,K,MModInts,MDivInts,Cs4-CsT)
    ).
fixInts_divmod([],_,[],[],Cs-Cs):-!.


fixInts_mod([Int|Ints],K,ModInts,CsH-CsT):-!,
    bcInteger:getUnaryNumber(Int,IntU),
    IntU=(Min,Max,_),
    %% Assert : possitive numbers only
    !,Min >= 0,!,
    (Max < K ->
        ModInts=[Int|MModInts],
        fixInts_mod(Ints,K,MModInts,CsH-CsT)
    ;
        K1 is K -1,
        bParser:new_int(ModInt,0,K1,CsH-Cs1),
        bParser:int_mod(Int,K,ModInt,Cs1-Cs2),
        ModInts=[ModInt|MModInts],
        fixInts_mod(Ints,K,MModInts,Cs2-CsT)
    ).
fixInts_mod([],_,[],Cs-Cs):-!.


decomposeSumModDivK_aux(Ints,N,K,SumMod,SumDivBits-SumDivBits,ConstrsH-ConstrsT):-
    N==1,!,% base cases
    Ints=[I1],
    bcInteger:getUnaryNumber(I1,I1U),
    I1U=(Min,Max,_),
    %% Assert : possitive numbers only
    !,Min >= 0,!,
    Max<K,!,
    SumMod=I1U,
    ConstrsH=ConstrsT.

decomposeSumModDivK_aux(Ints,N,K,SumMod,SumDivBitsH-SumDivBitsT,ConstrsH-ConstrsT):-
    N2 is N // 2,
    N1 is N - N2,
    auxLists:listSplit(N1,Ints,Ints1,Ints2),
    decomposeSumModDivK_aux(Ints1,N1,K,SumMod1,SumDivBitsH-SumDivBits1,ConstrsH-Constrs1),
    decomposeSumModDivK_aux(Ints2,N2,K,SumMod2,SumDivBits1-SumDivBits2,Constrs1-Constrs2),
    Sum3len is 2*K-2,
    auxUnarynum:unarynumNewInRange(0,Sum3len,Sum3),
    auxUnarynum:unarynumGEqK(Sum3,K,Sum3bit),
    SumDivBits2=[Sum3bit|SumDivBitsT],
    bcUnaryAdder:uadderSimplify1st(bc(_,[SumMod1, SumMod2, Sum3]), Constr, _),
    (Constr==none ->
        Constrs2=Constrs3
    ;
        Constrs2=[Constr|Constrs3]
    ),
    specialCaseMod(Sum3,K,SumMod,Constrs3-ConstrsT).

%% ---------- COMMON PART ---------- %%
   
% where K<=|X|< 2*K
specialCaseMod(X,K,XmodK,ConstrsH-ConstrsT):-
    X=(Min,Max,Bits,_),
    %assert for this code:
    !,Min==0, Max < 2*K,!,
    K1 is K - 1,
    auxLists:listSplit(K1,Bits,Bits1,[Y|Bits2]),
    auxUnarynum:unarynumNewInRange(0,K1,XmodK),
    XmodK=(0,K1,Bits3,_),
    bcITE:iteReifType(ITEType),
    mux2ite(Bits1,Bits2,-Y,Bits3,ITEType,ConstrsH-ConstrsT).
    
mux2ite([X|Xs],[Y|Ys],I,[Z|Zs],Type,[bc(Type,[I,X,Y,Z])|ConstrsH]-ConstrsT):-!,
    mux2ite(Xs,Ys,I,Zs,Type,ConstrsH-ConstrsT).
mux2ite([],[],_,[],_,Constrs-Constrs):-!.
mux2ite([],[Y|Ys],I,[Z|Zs],Type,[bc(Type,[I,-1,Y,Z])|ConstrsH]-ConstrsT):-!,
    mux2ite([],Ys,I,Zs,Type,ConstrsH-ConstrsT).
mux2ite([X|Xs],[],I,[Z|Zs],Type,[bc(Type,[I,X,-1,Z])|ConstrsH]-ConstrsT):-!,
    mux2ite(Xs,[],I,Zs,Type,ConstrsH-ConstrsT).
mux2ite([X|Xs],[Y|Ys],I,[],Type,[bc(Type,[I,X,Y,-1])|ConstrsH]-ConstrsT):-!,
    mux2ite(Xs,Ys,I,[],Type,ConstrsH-ConstrsT).
mux2ite([X|Xs],[],I,[],Type,[bc(Type,[I,X,-1,-1])|ConstrsH]-ConstrsT):-!,
    mux2ite(Xs,[],I,[],Type,ConstrsH-ConstrsT).
mux2ite([],[Y|Ys],I,[],Type,[bc(Type,[I,-1,Y,-1])|ConstrsH]-ConstrsT):-!,
    mux2ite([],Ys,I,[],Type,ConstrsH-ConstrsT).
