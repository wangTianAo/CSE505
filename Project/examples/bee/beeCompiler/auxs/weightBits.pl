% Author: Amit Metodi
% Last Updated: 30/08/2016

:- module(weightBits, [ ]).
:- use_module('auxLiterals').

%%% ----- Bits 2 Weighted Bits -----
bits2wbits([X|Xs],[(Xl,Xop,1)|WXs]):-!,
    lit2plit(X,Xl,Xop),
    bits2wbits(Xs,WXs).
bits2wbits([],[]):-!.


bits2wbits([X|Xs],[Xw|Xws],[(Xl,Xop,Xw)|WXs]):-!,
    lit2plit(X,Xl,Xop),
    bits2wbits(Xs,Xws,WXs).
bits2wbits([],[],[]):-!.


plits2wbits([(Xl,Xop)|Xs],[(Xl,Xop,1)|WXs]):-!,
    plits2wbits(Xs,WXs).
plits2wbits([],[]):-!.

%%% ----- General Weighted Bits to Possitive Weighted Bits -----
wbitsToPosWeights(WBits,PosWBits):-!,
    wbitsToPosWeights(WBits,0,NWBits,OnesFound),
    (OnesFound==0 ->
        PosWBits=NWBits
    ;
        PosWBits=[(1,1,OnesFound)|NWBits]
    ).

wbitsToPosWeights([(Xl,Xop,Xw)|WBits],SoFar,NWBits,OnesFound):-!,
   (ground(Xl) ->
        (Xl*Xop=:=1 ->
              SoFar1 is SoFar + Xw,
              wbitsToPosWeights(WBits,SoFar1,NWBits,OnesFound)
        ;
              wbitsToPosWeights(WBits,SoFar,NWBits,OnesFound)
        )
   ;
   (Xw > 0 ->
        NWBits=[(Xl,Xop,Xw)|MWBits],
        wbitsToPosWeights(WBits,SoFar,MWBits,OnesFound) ;
   (Xw < 0 ->
        NXw is -Xw,
        NXop is -Xop,
        NWBits=[(Xl,NXop,NXw)|MWBits],
        SoFar1 is SoFar + Xw,
        wbitsToPosWeights(WBits,SoFar1,MWBits,OnesFound)
   ;
   wbitsToPosWeights(WBits,SoFar,NWBits,OnesFound)
   ))).
wbitsToPosWeights([],OnesFound,[],OnesFound):-!.

%%% ----- Clean Weighted Bits -----

wbitsUpdate(PWbits,CurK,NewPWbits,NewK,Changed):-
    wbitsUpdate(PWbits,CurK,SPWbits,SK,Changed,NeedSort),
    (NeedSort==1 ->
        msort(SPWbits,SSPWbits),
        Changed=1,
        wbitsUpdate(SSPWbits,SK,NewPWbits,NewK,1)
    ;
        NewK=SK,
        NewPWbits=SPWbits
    ).

wbitsUpdate([(X1,Xop1,W1)|PWbits],CurK,NewPWbits,NewK,Changed,NeedSort):-!,
    (ground(X1) ->
        Changed=1,
        (X1*Xop1 =:= 1 ->
            UpdK is CurK + W1,
            wbitsUpdate(PWbits,UpdK,NewPWbits,NewK,Changed,NeedSort)
        ;
            wbitsUpdate(PWbits,CurK,NewPWbits,NewK,Changed,NeedSort)
        ) ;
    (var(X1) ->
        wbitsUpdate(PWbits,(X1,Xop1,W1),CurK,NewPWbits,NewK,Changed,NeedSort) ;
    lit2plit(X1,X1n,X1op),
    Xop1n is Xop1 * X1op,
    wbitsUpdate(PWbits,(X1n,Xop1n,W1),CurK,NewPWbits,NewK,Changed,NeedSort)
    )).
wbitsUpdate([],ChangeK,[],ChangeK,_,_):-!.

wbitsUpdate([(X2,X2op,W2)|PWbits],(X1,X1op,W1),CurK,NewPWbits,NewK,Changed,NeedSort):-!,
    (ground(X2) ->
        Changed=1,
        (X2*X2op =:= 1 ->
            UpdK is CurK + W2,
            wbitsUpdate(PWbits,(X1,X1op,W1),UpdK,NewPWbits,NewK,1,NeedSort)
        ;
            wbitsUpdate(PWbits,(X1,X1op,W1),CurK,NewPWbits,NewK,1,NeedSort)
        ) ;
    (var(X2) ->
        (X2 == X1 ->
             Changed=1,
             (X2op==X1op ->
                  W12 is W1 + W2,
                  wbitsUpdate(PWbits,(X1,X1op,W12),CurK,NewPWbits,NewK,1,NeedSort)
             ;
                  (W1==W2 ->
                      UpdK is CurK + W1,
                      NeedSort=1,
                      wbitsUpdate(PWbits,UpdK,NewPWbits,NewK,1,1) ;
                  (W1 > W2 ->
                      W12 is W1 - W2,
                      UpdK is CurK + max(W1,W2) - W12,
                      wbitsUpdate(PWbits,(X1,X1op,W12),UpdK,NewPWbits,NewK,1,NeedSort)
                  ;
                      W12 is W2 - W1,
                      UpdK is CurK + max(W1,W2) - W12,
                      wbitsUpdate(PWbits,(X2,X2op,W12),UpdK,NewPWbits,NewK,1,NeedSort)
                  ))
             )
        ;
            (X2 @< X1 -> NeedSort=1 ; true),
            NewPWbits=[(X1,X1op,W1)|MorePWbits],
            wbitsUpdate(PWbits,(X2,X2op,W2),CurK,MorePWbits,NewK,Changed,NeedSort)
        )
    ;
        lit2plit(X2,X2n,X2opb),
        X2opn is X2op*X2opb,
        wbitsUpdate([(X2n,X2opn,W2)|PWbits],(X1,X1op,W1),CurK,NewPWbits,NewK,Changed,NeedSort)
    )).
wbitsUpdate([],PWx,ChangeK,[PWx],ChangeK,_,_):-!.



wbitsRemoveFalses([(Xl,Xop,_)|Xs],Ys):-
    ground(Xl), Xl*Xop =:= -1,!,
    wbitsRemoveFalses(Xs,Ys).
wbitsRemoveFalses([X|Xs],[X|Ys]):-!,
    wbitsRemoveFalses(Xs,Ys).
wbitsRemoveFalses([],[]):-!.

wbitsAsgnFalses([(Xl,Xop,_)|Xs]):-!,
    plitAsgnFalse((Xl,Xop)),
    wbitsAsgnFalses(Xs).
wbitsAsgnFalses([]):-!.

wbitsAsgnTrues([(Xl,Xop,_)|Xs]):-!,
    plitAsgnTrue((Xl,Xop)),
    wbitsAsgnTrues(Xs).
wbitsAsgnTrues([]):-!.




wbitsToBuckets(WBits,Buckets):-
    wbitsMoveWeight(WBits,WBitsW1st),
    msort(WBitsW1st,SWBits),
    wbitsToBuckets_(SWBits,Buckets).
    
wbitsToBuckets_([(W,B)|WBits],[[W,B|Bucket]|Buckets]):-!,
    wbitsToBuckets_w(WBits,W,Bucket,RWBits),
    wbitsToBuckets_(RWBits,Buckets).
wbitsToBuckets_([],[]):-!.

wbitsToBuckets_w([(W,B)|WBits],W,[B|Bucket],RWBits):-!,
    wbitsToBuckets_w(WBits,W,Bucket,RWBits).
wbitsToBuckets_w(WBits,_,[],WBits):-!.


wbitsMoveWeight([(Xl,Xop,W)|WBits],[(W,X)|BitsW1st]):-!,
   (Xop=:=1 ->
       X = Xl
   ;
       X = -Xl
   ),
   wbitsMoveWeight(WBits,BitsW1st).
wbitsMoveWeight([],[]):-!.