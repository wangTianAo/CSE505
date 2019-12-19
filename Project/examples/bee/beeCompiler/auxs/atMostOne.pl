% Author: Amit Metodi
% Last Updated: 18/03/2012

:- module(atMostOne, [ ]).
:- use_module('auxLiterals').


atMostOneSimplify(Pbits,NewPbits,FoundOne,Changed):-!,
    atMostOneSimplify(Pbits,TPbits,FoundOne,Changed,NeedSort),
    (FoundOne==1 ->
         plitAsgnFalses(TPbits),!,
         NewPbits=[] ;
%    (FoundOne==2 ->
%         append(FalseBits1,[X,Y],TPbits),!,
%         plitAsgnFalses(FalseBits1),
%         NewPbits=[X,Y] ;
    (NeedSort==1 ->
        msort(TPbits,TPbits2),
        Changed=1,
        atMostOneSimplify(TPbits2,NewPbits,FoundOne,_) ;
    NewPbits=TPbits
%    )
    )).

atMostOneSimplify([(X1,Xop1)|PWbits],NewPWbits,FoundOne,Changed,NeedSort):-!,
    (ground(X1) ->
        Changed=1,
        (X1*Xop1 =:= 1 ->
            FoundOne=1,
            NewPWbits=PWbits
        ;
            atMostOneSimplify(PWbits,NewPWbits,FoundOne,1,NeedSort)
        ) ;
    (var(X1) ->
        atMostOneSimplify(PWbits,(X1,Xop1),NewPWbits,FoundOne,Changed,NeedSort) ;
    lit2plit(X1,X1n,X1op),
    Xop1n is Xop1 * X1op,
    atMostOneSimplify(PWbits,(X1n,Xop1n),NewPWbits,FoundOne,Changed,NeedSort)
    )).
atMostOneSimplify([],[],_,_,_):-!.

atMostOneSimplify([(X2,X2op)|PWbits],(X1,X1op),NewPWbits,FoundOne,Changed,NeedSort):-!,
    (ground(X2) ->
        Changed=1,
        (X2*X2op =:= 1 ->
            FoundOne=1,
            NewPWbits=[(X1,X1op)|PWbits]
        ;
            atMostOneSimplify(PWbits,(X1,X1op),NewPWbits,FoundOne,1,NeedSort)
        ) ;
    (var(X2) ->
        (X2 == X1 ->
             Changed=1,
             (X2op==X1op ->
                  plitAsgnFalse((X2,X2op)),!,
                  atMostOneSimplify(PWbits,NewPWbits,FoundOne,1,NeedSort)
             ;
%                  FoundOne=2,
%                  plitAsgnFalses(PWbits),!,
%                  NewPWbits=[(X1,X1op),(X2,X2op)]
                  FoundOne=1,
                  NewPWbits=PWbits
             )
        ;
            (X2 @>= X1 ->
                  NewPWbits=[(X1,X1op)|MorePWbits],
                  atMostOneSimplify(PWbits,(X2,X2op),MorePWbits,FoundOne,Changed,NeedSort)
            ;
                  NeedSort=1,
                  NewPWbits=[(X2,X2op)|MorePWbits],
                  atMostOneSimplify(PWbits,(X1,X1op),MorePWbits,FoundOne,Changed,NeedSort)
            )
        )
    ;
        lit2plit(X2,X2n,X2opb),
        X2opn is X2op*X2opb,
        atMostOneSimplify([(X2n,X2opn)|PWbits],(X1,X1op),NewPWbits,FoundOne,Changed,NeedSort)
    )).

atMostOneSimplify([],PWx,[PWx],_,_,_):-!.
