% Author: Amit Metodi
% Date: 21/10/2011

:- module(xorVec, [ ]).
:- use_module('auxLiterals').

xorSimplify(Pbits,NewPbits,Changed):-!,
    xorSimplify(Pbits,0,NPbits,OsCnt,Changed,NeedSort),
    Mod2 is OsCnt mod 2,
    (Mod2 == 1 ->
        (NPbits=[(Fl,Fop)|MSPbits] ->
            FopFlip is Fop * -1,
            (NeedSort==1 ->
                msort([(Fl,FopFlip)|MSPbits],SNPbits),
                Changed=1,
                xorSimplify(SNPbits,NewPbits,Changed)
            ;
                xorSimplify([(Fl,FopFlip)|MSPbits],NewPbits,Changed)
            )
        ;
            NewPbits=[(1,1)]
        )
    ;
        (NeedSort==1 ->
            msort(NPbits,SNPbits),
            Changed=1,
            xorSimplify(SNPbits,NewPbits,Changed)
        ;
            NewPbits=NPbits
        )
    ).


xorSimplify([(X1,Xop1)|PWbits],CurK,NewPWbits,NewK,Changed,NeedSort):-!,
    (ground(X1) ->
        Changed=1,
        (X1*Xop1 =:= 1 ->
            UpdK is CurK + 1,
            xorSimplify(PWbits,UpdK,NewPWbits,NewK,1,NeedSort)
        ;
            xorSimplify(PWbits,CurK,NewPWbits,NewK,1,NeedSort)
        ) ;
    (var(X1) ->
        xorSimplify(PWbits,(X1,Xop1),CurK,NewPWbits,NewK,Changed,NeedSort) ;
    lit2plit(X1,X1n,X1op),
    Xop1n is Xop1 * X1op,
    xorSimplify(PWbits,(X1n,Xop1n),CurK,NewPWbits,NewK,Changed,NeedSort)
    )).
xorSimplify([],ChangeK,[],ChangeK,_,_):-!.

xorSimplify([(X2,X2op)|PWbits],(X1,X1op),CurK,NewPWbits,NewK,Changed,NeedSort):-!,
    (ground(X2) ->
        Changed=1,
        (X2*X2op =:= 1 ->
            UpdK is CurK + 1,
            xorSimplify(PWbits,(X1,X1op),UpdK,NewPWbits,NewK,1,NeedSort)
        ;
            xorSimplify(PWbits,(X1,X1op),CurK,NewPWbits,NewK,1,NeedSort)
        ) ;
    (var(X2) ->
        (X2 == X1 ->
             Changed=1,
             NeedSort=1,
             (X2op==X1op ->
                  NeedSort=1,
                  xorSimplify(PWbits,CurK,NewPWbits,NewK,1,NeedSort)
             ;
                  UpdK is CurK + 1,
                  xorSimplify(PWbits,UpdK,NewPWbits,NewK,1,NeedSort)
             )
        ;
            (X2 @> X1 ->
                  NewPWbits=[(X1,X1op)|MorePWbits],
                  xorSimplify(PWbits,(X2,X2op),CurK,MorePWbits,NewK,Changed,NeedSort)
            ;
                  NeedSort=1,
                  NewPWbits=[(X2,X2op)|MorePWbits],
                  xorSimplify(PWbits,(X1,X1op),CurK,MorePWbits,NewK,Changed,NeedSort)
            )
        )
    ;
        lit2plit(X2,X2n,X2opb),
        X2opn is X2op*X2opb,
        xorSimplify([(X2n,X2opn)|PWbits],(X1,X1op),CurK,NewPWbits,NewK,Changed,NeedSort)
    )).

xorSimplify([],PWx,ChangeK,[PWx],ChangeK,_,_):-!.
