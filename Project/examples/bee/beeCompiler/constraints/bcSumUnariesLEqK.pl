% Author: Amit Metodi
% Last Updated: 22/07/2012

:- module(bcSumUnariesLEqK, [ ]).
:- use_module('../auxs/auxLiterals').
%:- use_module('../auxs/auxUnarynum').
%:- use_module('../auxs/weightUnaries').

/*
TODO:
  * GCD @ advance simplify
  * Flip to GEq and Decompose when it will generate a smaller CNF
*/

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
% ----- int_array_lin_rel -----
:- Head=int_array_lin_leq(Weights,Ints,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       weightUnaries:wunariesFix2PosWghtInt([1|Weights],[-Sum|Ints],WInts,0,LEqTo),
       bcSumUnariesLEqK:sumUnariesLEqKType(Type),
       bcSumUnariesLEqK:sumUnariesLEqKSimplify(bc(Type,[LEqTo|WInts]),Constr,1),
       (Constr==none ->
            ConstrsH=ConstrsT
       ;
            ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_array_lin_lt(Weights,Ints,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       weightUnaries:wunariesFix2PosWghtInt([1|Weights],[-Sum|Ints],WInts,-1,LEqTo),
       bcSumUnariesLEqK:sumUnariesLEqKType(Type),
       bcSumUnariesLEqK:sumUnariesLEqKSimplify(bc(Type,[LEqTo|WInts]),Constr,1),
       (Constr==none ->
            ConstrsH=ConstrsT
       ;
            ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_array_lin_geq(Weights,Ints,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       bcSumUnariesLEqK:negConsts(Weights,NWeights),
       bParser:int_array_lin_leq(NWeights,Ints,-Sum,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_array_lin_gt(Weights,Ints,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       bcSumUnariesLEqK:negConsts(Weights,NWeights),
       bParser:int_array_lin_lt(NWeights,Ints,-Sum,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).


% ----- int_array_sum_rel -----
:- Head=int_array_sum_leq(Ints,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       weightUnaries:wunariesFix2PosWghtInt([-Sum|Ints],WInts,0,LEqTo),
       bcSumUnariesLEqK:sumUnariesLEqKType(Type),
       bcSumUnariesLEqK:sumUnariesLEqKSimplify(bc(Type,[LEqTo|WInts]),Constr,1),
       (Constr==none ->
            ConstrsH=ConstrsT
       ;
            ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_array_sum_lt(Ints,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       weightUnaries:wunariesFix2PosWghtInt([-Sum|Ints],WInts,-1,LEqTo),
       bcSumUnariesLEqK:sumUnariesLEqKType(Type),
       bcSumUnariesLEqK:sumUnariesLEqKSimplify(bc(Type,[LEqTo|WInts]),Constr,1),
       (Constr==none ->
            ConstrsH=ConstrsT
       ;
            ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_array_sum_geq(Ints,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       bcSumUnariesLEqK:negInts(Ints,NInts),
       bParser:int_array_sum_leq(NInts,-Sum,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_array_sum_gt(Ints,Sum,ConstrsH-ConstrsT),
   Body=(
       !,
       bcSumUnariesLEqK:negInts(Ints,NInts),
       bParser:int_array_sum_lt(NInts,-Sum,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).



negConsts([X|Xs],[Y|Ys]):-!,
    Y is -X,
    negConsts(Xs,Ys).
negConsts([],[]):-!.

negInts([X|Xs],[-X|Ys]):-!,
    negInts(Xs,Ys).
negInts([],[]):-!.

%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
sumUnariesLEqKType([
             bcSumUnariesLEqK:sumUnariesLEqKSimplify,
             bcSumUnariesLEqK:sumUnariesLEqKSimplifyAdv,
             bcSumUnariesLEqK:sumUnariesLEqKDecompose,
             0,
             sumUnariesLEqK
            ]):-!.

%%% ----- Simplify ----- %%%
sumUnariesLEqKSimplify(Constr,NewConstr,Changed):-!,
    Constr=bc(Type,[LEqTo|WInts]),
    weightUnaries:wunairesUpdate(WInts,0,NWInts,OnesFound,Changed),
    (Changed==1 ->
       NLEqTo is LEqTo - OnesFound,
       (NLEqTo>=0 ->
          sumUnariesLEqKSimplify_ub(NWInts,NLEqTo,0,Max,FWInts,Changed2),
          (Max > NLEqTo ->
              (FWInts=[Int1,Int2] ->
                  Int1=(Weight1,UInt1),
                  Weight1m is -Weight1,
                  auxUnarynum:unarynumMulByConst((0,UInt1),Weight1m,Au),
                  auxUnarynum:unarynumAddConst(Au,NLEqTo,FAu),
                  Int2=(Weight2,UInt2),
                  auxUnarynum:unarynumMulByConst((0,UInt2),Weight2,Bu),
                  bcUnaryLEq:unaryLEqType(LEqType),
                  bcUnaryLEq:unaryLEqSimplify(bc(LEqType,[Bu,FAu]), NewConstr, 1) ;
              (Changed2==1 ->
                  sumUnariesLEqKSimplify(bc(Type,[NLEqTo|FWInts]),NewConstr,_)
              ;
                  NewConstr=bc(Type,[NLEqTo|FWInts])
              ))
          ;
              NewConstr=none
          )
       ;
       throw(unsat)
       )
    ;
    NewConstr=Constr
    ).

sumUnariesLEqKSimplify_ub([(Weight,Max,Bits)|WInts],LEqTo,CurTtl,TtlMax,NWInts,Changed):-!,
    CurMax is Max*Weight,
    (CurMax =< LEqTo ->
        UpdTtl is CurTtl + CurMax,
        NWInts=[(Weight,Max,Bits)|MWInts],
        sumUnariesLEqKSimplify_ub(WInts,LEqTo,UpdTtl,TtlMax,MWInts,Changed)
    ;
        Changed=1,
        NMax is LEqTo // Weight,!,
        (NMax > 0 ->
            auxUnarynum:unarynumSetMax((0,Max,Bits),NMax,(0,NMax,NBits)),
            UpdTtl is CurTtl + NMax*Weight,
            NWInts=[(Weight,NMax,NBits)|MWInts],
            sumUnariesLEqKSimplify_ub(WInts,LEqTo,UpdTtl,TtlMax,MWInts,Changed)
        ;
            Bits=(XBits,_),
            auxLiterals:litAsgnFalses(XBits),
            sumUnariesLEqKSimplify_ub(WInts,LEqTo,CurTtl,TtlMax,NWInts,Changed)
        )
    ).
sumUnariesLEqKSimplify_ub([],_,Max,Max,[],_):-!.


%%% ----- Advance Simplify ----- %%%
sumUnariesLEqKSimplifyAdv(Constr,NewConstr,Changed):-
    Constr=bc(Type,[LEqTo|WInts]),
    bcSumUnaries:extractMax1(WInts,RWInts,WBits),
    (RWInts=[] ->
         Changed=1,
         bcSumBitsLEqK:sumBitsLEqKType(BitsType),
         bcSumBitsLEqK:sumBitsLEqKSimplify_step1(bc(BitsType,[LEqTo|WBits]),NewConstr,1) ;
%    (RWInts=[X] ->
         %% TODO switch to SumBitsLEqInt
    ((WBits=[] ; WBits=[_]) ->
         %%% TODO GCD(WInts)
         NewConstr=Constr ;
         
    msort(WBits,SWBits),
    bcSumUnaries:simplifyWBits(SWBits,LEqTo,FWBits,FLEqTo,Changed),
    (Changed==1 ->
        bcSumUnaries:unifyWBits2Ints(FWBits,RWInts,NWInts),
        %%% TODO GCD(NWInts)
        bcSumUnariesLEqK:sumUnariesLEqKSimplify(bc(Type,[FLEqTo|NWInts]),NewConstr,1) %% Because "special" case
        %Constr=bc(Type,[FLEqTo|NWInts]
    ;
       %%% TODO GCD(WInts)
       NewConstr=Constr
    ))).

%%% ----- Decompose ----- %%%
sumUnariesLEqKDecompose(bc(_Type,[LEqTo|WInts]),Constrs):-!,
    msort(WInts,SWInts),
    bcSumUnaries:extractMax1(SWInts,RWInts,WBits),
    ((WBits=[] ; WBits=[_]) ->
        length(SWInts,IntsCnt),
        createOddEvenSum_leqK(SWInts,IntsCnt,LEqTo,Constrs-[])
    ;
        bcSumUnaries:sumWBitsWeights(WBits,0,WBitsMax),
        WBitsUB is min(WBitsMax,LEqTo),
        auxUnarynum:unarynumNewInRange(0,WBitsUB,(0,WBsum)),
        bcSumBits:sumBitsType(BitSumType),
        Constrs=[bc(BitSumType,[(0,WBsum),(1,-1,1)|WBits])|ConstrsM],
        length([(1,WBsum)|RWInts],IntsCnt),
        createOddEvenSum_leqK([(1,WBsum)|RWInts],IntsCnt,LEqTo,ConstrsM-[])
    ).


createOddEvenSum_leqK(WInts,WIntsCnt,LEqTo,ConstrsH-ConstrsT):-!,
    bcUnaryAdder:uadderType(AdderType),
    bcSumUnaries:splitIntsList(WInts,WIntsCnt,WInts1,L1,WInts2,L2),
    bcSumUnaries:createOddEvenSum(WInts1,L1,Sum1,LEqTo,AdderType,ConstrsH-ConstrsM1),!,
    bcSumUnaries:createOddEvenSum(WInts2,L2,Sum2,LEqTo,AdderType,ConstrsM1-[Constr|ConstrsT]),!,

    auxUnarynum:unarynumNeg(Sum2,Sum2Neg),
    auxUnarynum:unarynumAddConst(Sum2Neg,LEqTo,(S2Min,S2Max,S2Bits,S2Lbit)),

    bcUnaryLEq:unaryLEqType(LEqType),
    S2MinF is S2Min - 1,
    Constr=bc(LEqType,[Sum1,(S2MinF,S2Max,[1|S2Bits],S2Lbit)]).