% Author: Amit Metodi
% Last Updated: 15/04/2012

:- module(bcUnaryDirectChnl, []).
:- use_module('../auxs/auxLiterals').
%:- use_module('../auxs/atMostOne').

/**
  TODO:
   * write more efficient simplify
*/

chnlU2DType([
            bcUnaryDirectChnl:unary2directSimplify,
            skipSimplify,
            0,
            bcUnaryDirectChnl:unary2direct2cnf,
            chnlUnaryDirect
           ]).

unary2directSimplify(bc(Type,[U,D,Dpb]), Constr, Changed):-!,
       atMostOne:atMostOneSimplify(Dpb,NDpb,_,Changed),
       bcSorted:simplifySorted_s(U, _, Changed),
       u2dSimplify_s1(U,D,NU,ND,Drop),
       (Drop==1 -> litAsgnFalses(ND), litAsgnTrues(NU), Constr=none ;
       (Changed==1 ->
           (NU=[] -> ND=[D0], litAsgnTrue(D0), Constr=none ;
           (NU=[U1] -> ND=[D0,D1], litUnify(U1,D1), litUnify(-U1,D0), Constr=none ;
           (NU=[U1,U2] ->
               ND=[D0,_,D2],
               litUnify(-U1,D0),
               litUnify(U2,D2),
               lits2plits(ND,Vec),
               bcExactlyOne:exoType(EXOtype),
               bcExactlyOne:exoSimplify(bc(EXOtype,Vec),Constr,_) ;
           unary2directSimplify(bc(Type,[NU,ND,NDpb]), Constr, _)
           )))
       ;
          Constr=bc(Type,[U,D,NDpb])
       )).

u2dSimplify_s1([U1|Us],[D0|D],NU,ND,Drop):-!,
       litUnify(D0,-U1),
       (ground(U1) ->
            (U1 =:= 1 ->
                u2dSimplify_s1(Us,D,NU,ND,Drop)
            ;
                Drop=1,
                ND=D,
                NU=[],
                litAsgnFalses(Us)
            ) ;
       ND=[D0|MD],
       u2dSimplify_s2(Us,U1,D,NU,MD,Drop)
       ).
u2dSimplify_s1([],[D0],[],[],1):-!,
       litAsgnTrue(D0).

u2dSimplify_s2([U2|Us],U1,[D1|D],NU,ND,Drop):-!,
       (ground(D1) ->
            (D1 =:= -1 ->
                litUnify(U1,U2),
                u2dSimplify_s2(Us,U2,D,NU,ND,Drop)
            ;
                Drop=1,
                NU=[],
                ND=D,
                litAsgnTrue(U1),
                litAsgnFalses([U2|Us])
            ) ;
       (ground(U2) ->
            (U2 =:= -1 ->
                litAsgnFalses(Us),
                litAsgnFalses(D),
                litUnify(U1,D1),
                NU=[U1],
                ND=[U1]
            ;
                !,fail
                %throw(bug(simplify,unaryDirectCnl('bad assumption'))),
                %litAsgnFalse(D1),
                %u2dSimplify_s2(Us,1,D,NU,ND,Drop)
            ) ;
       (litIsEqual(U1,U2) ->
            litAsgnFalse(D1),
            u2dSimplify_s2(Us,U2,D,NU,ND,Drop) ;
       (litIsEqual(U1,-U2) ->
            Drop=1,
            NU=[],
            ND=D,
            litAsgnTrue(U1),
            litAsgnTrue(D1),
            litAsgnFalses(Us) ;
       NU=[U1|MU],
       ND=[D1|MD],
       u2dSimplify_s2(Us,U2,D,MU,MD,Drop)
       )))).
u2dSimplify_s2([],U1,[D1],NU,ND,Drop):-!,
       (ground(D1) ->
            (D1 =:= -1 ->
                NU=[],
                ND=[],
                litAsgnFalse(U1)
            ;
                Drop=1,
                NU=[U1],
                ND=[]
            ) ;
       NU=[U1],
       ND=[D1],
       litUnify(U1,D1)
       ).


unary2direct2cnf(bc(_,[U,[_|D],_]), CnfH-CnfT):-!,
       unary2directCnf(D,U,CnfH-CnfT).

unary2directCnf([D1|Ds],[U1,U2|Us],CnfH-CnfT):-!,
       CnfH=[
             % U2 -> U1
             [U1, -U2],
             % U1 & -U2 -> D1
             [-U1, U2, D1],
             % D1 -> U1
             [U1, -D1],
             % D1 -> -U2
             [-U2, -D1]
             |CnfM],
       unary2directCnf(Ds,[U2|Us],CnfM-CnfT).
unary2directCnf([_],[_],Cnf-Cnf):-!.