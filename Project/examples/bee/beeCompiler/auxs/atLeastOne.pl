% Author: Amit Metodi
% Last Updated: 12/03/2016

:- module(atLeastOne, [ ]).
:- use_module('auxLiterals').


atLeastOneSimplify(Pbits,NewPbits,FoundOne,Changed):-!,
    atLeastOneSimplify(Pbits,TPbits,FoundOne,Changed,NeedSort),
    (FoundOne==1 -> NewPbits=[] ;
    (NeedSort==1 ->
        sort(TPbits,TPbits2),
        Changed=1,
        atLeastOneSimplify(TPbits2,NewPbits,FoundOne,_) ;
    NewPbits=TPbits
    )).

atLeastOneSimplify([PX1|PWbits],NewPWbits,FoundOne,Changed,NeedSort):-!,
    PX1=(X1,Xop1),
    (ground(X1) ->
        Changed=1,
        (X1*Xop1 =:= 1 ->
            FoundOne=1
        ;
            atLeastOneSimplify(PWbits,NewPWbits,FoundOne,1,NeedSort)
        ) ;
    (var(X1) ->
        atLeastOneSimplify(PWbits,PX1,NewPWbits,FoundOne,Changed,NeedSort) ;
    lit2plit(X1,X1n,X1op),
    Xop1n is Xop1 * X1op,
    atLeastOneSimplify(PWbits,(X1n,Xop1n),NewPWbits,FoundOne,Changed,NeedSort)
    )).
atLeastOneSimplify([],[],_,_,_):-!.

atLeastOneSimplify([PX2|PWbits],PX1,NewPWbits,FoundOne,Changed,NeedSort):-!,
    PX2=(X2,X2op),
    (ground(X2) ->
        Changed=1,
        (X2*X2op =:= 1 ->
            FoundOne=1
        ;
            atLeastOneSimplify(PWbits,PX1,NewPWbits,FoundOne,1,NeedSort)
        ) ;
    (var(X2) ->
        PX1=(X1,X1op),
        (X2 == X1 ->
             Changed=1,
             (X2op==X1op ->
                  atLeastOneSimplify(PWbits,PX1,NewPWbits,FoundOne,1,NeedSort)
             ;
                  FoundOne=1
             )
        ;
            (X2 @< X1 ->
                  NeedSort=1,
                  NewPWbits=[PX2|MorePWbits],
                  atLeastOneSimplify(PWbits,PX1,MorePWbits,FoundOne,Changed,NeedSort)
            ;
                  NewPWbits=[PX1|MorePWbits],
                  atLeastOneSimplify(PWbits,PX2,MorePWbits,FoundOne,Changed,NeedSort)
            )
        )
    ;
        lit2plit(X2,X2n,X2opb),
        X2opn is X2op*X2opb,
        atLeastOneSimplify([(X2n,X2opn)|PWbits],PX1,NewPWbits,FoundOne,Changed,NeedSort)
    )).

atLeastOneSimplify([],PWx,[PWx],_,_,_):-!.
