% Literal Support
% Author: Amit Metodi
% Date: 06/03/2016

:- module(auxLiterals, [
                   litAsgnTrue/1, litAsgnTrue/2,
                   litAsgnFalse/1, litAsgnFalse/2,
                   litUnify/2, litUnify/3,
                   litAsgnTrues/1,
                   litAsgnFalses/1,
                   litUnifies/2,
                   litUnifiesWfalses/2,
                   litUnifiesAsNotBs/2,
                   litNotXs/2,
                   litNotReverseXs/2,
                   litIsEqual/2,

                   lit2plit/3,   plit2lit/2,
                   lits2plits/2, plits2lits/2,
                   lit2lit/2,    plit2plit/4,
                   
                   plitAsgnTrue/1, plitAsgnTrues/1,
                   plitAsgnFalse/1, plitAsgnFalses/1,
                   plitUnify/2,     plitUnifyDiff/2,
				   plitNotXs/2
                   ]).
                   
litAsgnTrue(X):-X is 1,!.
litAsgnTrue(-(X)):-!,litAsgnFalse(X).
litAsgnTrue(_):-!,throw(unsat).

litAsgnFalse(X):-X is -1, !.
litAsgnFalse(-X):-!,litAsgnTrue(X).
litAsgnFalse(_):-!,throw(unsat).

litAsgnTrue(X,Changed):-!,
    (ground(X) ->
         (X =:= 1,! ; throw(unsat))
    ;
         Changed=1,!,
         litAsgnTrue(X)).

litAsgnFalse(X,Changed):-!,
    (ground(X) ->
         (X =:= -1,! ; throw(unsat))
    ;
         Changed=1,!,
         litAsgnFalse(X)).

litUnify(A,B):-
    (ground(A) ->
        (ground(B) -> (A=:=B,! ; throw(unsat)) ;
        litPureLit_(B,Bl,Bop),
        Bl is A*Bop );
    (ground(B) ->
        litPureLit_(A,Al,Aop),
        Al is B*Aop ;
    litPureLit_(A,Al,Aop),
    litPureLit_(B,Bl,Bop),!,
    (Aop==Bop ->
         Al=Bl
    ;
         (Al @> Bl -> Al= -Bl;
         (Al @< Bl -> Bl= -Al;
         !,throw(unsat)))
    ))).

litUnify(A,B,Changed):-
    (ground(A) ->
        (ground(B) -> (A=:=B,! ; throw(unsat)) ;
        Changed=1,
        litPureLit_(B,Bl,Bop),
        Bl is A*Bop ) ;
    (ground(B) ->
        Changed=1,
        litPureLit_(A,Al,Aop),
        Al is B*Aop ;
    litPureLit_(A,Al,Aop),
    litPureLit_(B,Bl,Bop),!,
    (Aop==Bop ->
         (Al\==Bl ->
            Changed=1,
            Al=Bl ;
            true)
    ;
         (Al @> Bl -> Al= -Bl;
         (Al @< Bl -> Bl= -Al;
         !,throw(unsat))),
         Changed=1
    ))).


litAsgnTrues([X|Xs]):-!,
    litAsgnTrue(X),!,
    litAsgnTrues(Xs).
litAsgnTrues([]):-!.

litAsgnFalses([X|Xs]):-!,
    litAsgnFalse(X),!,
    litAsgnFalses(Xs).
litAsgnFalses([]):-!.

litUnifies([A|As],[B|Bs]):-!,
    litUnify(A,B),
    litUnifies(As,Bs).
litUnifies([],[]):-!.

litUnifiesWfalses([A|As],[B|Bs]):-!,
    litUnify(A,B),!,
    litUnifiesWfalses(As,Bs).
litUnifiesWfalses([],[]):-!.
litUnifiesWfalses([A|As],[]):-!,litAsgnFalses_safe([A|As]).
litUnifiesWfalses([],[A|As]):-!,litAsgnFalses_safe([A|As]).

litAsgnFalses_safe([]):-!.
litAsgnFalses_safe([X|Xs]):-!,
    litAsgnFalse(X),!,
    litAsgnFalses_safe(Xs).

litUnifiesAsNotBs([A|As],[B|Bs]):-!,
     litUnify(B,-A),!,
     litUnifiesAsNotBs(As,Bs).
litUnifiesAsNotBs([],[]):-!.

litNotXs([A|As],[-A|Bs]):-!,
     litNotXs(As,Bs).
litNotXs([],[]):-!.

litNotReverseXs(Xs,Ys):-!,
     litNotReverseXs(Xs,[],Ys).
litNotReverseXs([A|As],Bs,Ys):-!,
     litNotReverseXs(As,[-A|Bs],Ys).
litNotReverseXs([],Ys,Ys):-!.



litIsEqual(A,B) :-
    % when A is True/False
    (ground(A) ->
         !,ground(B),!, A=:=B ;
    % when B is True/False (A isn't ground)
    (ground(B) ->
         !,fail ;
    % when A and B literals
    litPureLit_(A,Al,Aop),
    litPureLit_(B,Bl,Bop),!,
    Al==Bl, Aop==Bop
    )).



lit2plit(X,Xl,XOp):-!,
    (ground(X) ->
         Xl=1, XOp is sign(X)
    ;
         litPureLit_(X,Xl,XOp)
    ).
litPureLit_(X,X,1):-var(X),!.
litPureLit_(-(X),X,-1):-var(X),!.
litPureLit_(-(-(X)),Xl,Xop):-!,litPureLit_(X,Xl,Xop).

plit2lit((Xl,Xop),X):-!,
    (ground(Xl) ->
        X is Xl*Xop ;
    (var(Xl) ->
        (Xop == 1 -> X=Xl ; X= -Xl) ;
    litPureLit_(Xl,Zl,Zop),
    (Xop*Zop =:= 1 -> X=Zl ; X= -Zl)
    )).

lits2plits([X|Xs],[(Xl,Xop)|PXs]):-!,
    lit2plit(X,Xl,Xop),!,
    lits2plits(Xs,PXs).
lits2plits([],[]):-!.

plits2lits([X|Xs],[PX|PXs]):-!,
    plit2lit(X,PX),!,
    plits2lits(Xs,PXs).
plits2lits([],[]):-!.

lit2lit(X,Z):-!,
   (ground(X) ->
       Z is X
   ;
       litPureLit_(X,Xl,Xop),
       (Xop == 1 -> Z= Xl ; Z= -Xl)
   ).

plit2plit(Xl,Xop,Zl,Zop):-
   (var(Xl) -> Zl=Xl, Zop=Xop ;
   (ground(Xl) ->
       Zl= 1,
       Zop is sign(Xl)*Xop ;
   litPureLit_(Xl,Zl,Wop),
   Zop is Xop*Wop
   )).



plitAsgnTrue((Xl,1)):-!,litAsgnTrue(Xl).
plitAsgnTrue((Xl,-1)):-!,litAsgnFalse(Xl).
plitAsgnFalse((Xl,1)):-!,litAsgnFalse(Xl).
plitAsgnFalse((Xl,-1)):-!,litAsgnTrue(Xl).

plitAsgnFalses([X|Xs]):-!,
    plitAsgnFalse(X),
    plitAsgnFalses(Xs).
plitAsgnFalses([]):-!.

plitAsgnTrues([X|Xs]):-!,
    plitAsgnTrue(X),
    plitAsgnTrues(Xs).
plitAsgnTrues([]):-!.


plitUnify((X1l,X1op),(X2l,X2op)):-!,
    ((var(X1l),var(X2l)) ->
        (X1op=:=X2op ->
            X1l=X2l
        ;
             (X1l @> X2l -> X1l= -X2l;
             (X1l @< X2l -> X2l= -X1l;
             !,throw(unsat)))
        ) ;
    (ground(X1l) ->
        (X1l*X1op =:= 1 ->
           plitAsgnTrue((X2l,X2op))
        ;
           plitAsgnFalse((X2l,X2op))
        ) ;
    (ground(X2l) ->
        (X2l*X2op =:= 1 ->
           plitAsgnTrue((X1l,X1op))
        ;
           plitAsgnFalse((X1l,X1op))
        ) ;
    plit2plit(X1l,X1op,Z1l,Z1op),
    plit2plit(X2l,X2op,Z2l,Z2op),
    plitUnify((Z1l,Z1op),(Z2l,Z2op))
    ))).

plitUnifyDiff((X1l,X1op),(X2l,X2op)):-!,
    ((var(X1l),var(X2l)) ->
        (X1op=:=X2op ->
             (X1l @> X2l -> X1l= -X2l;
             (X1l @< X2l -> X2l= -X1l;
             !,throw(unsat)))
        ;
            X1l=X2l
        ) ;
    (ground(X1l) ->
        (X1l*X1op =:= 1 ->
           plitAsgnFalse((X2l,X2op))
        ;
           plitAsgnTrue((X2l,X2op))
        ) ;
    (ground(X2l) ->
        (X2l*X2op =:= 1 ->
           plitAsgnFalse((X1l,X1op))
        ;
           plitAsgnTrue((X1l,X1op))
        ) ;
    plit2plit(X1l,X1op,Z1l,Z1op),
    plit2plit(X2l,X2op,Z2l,Z2op),
    plitUnifyDiff((Z1l,Z1op),(Z2l,Z2op))
    ))).

	
plitNotXs([(X1l,X1op)|Xs],[(X1l,NX1op)|NXs]):-!,
    NX1op is -X1op,
    plitNotXs(Xs,NXs).
plitNotXs([],[]):-!.