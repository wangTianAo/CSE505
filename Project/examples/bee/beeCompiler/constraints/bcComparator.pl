% Author: Amit Metodi
% Last Updated: 11/01/2012

:- module(bcComparator, [ ]).
:- use_module('../auxs/auxLiterals').

%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
comparatorType([
                bcComparator:comparatorSimplify,
                skipSimplify,
                0,
                bcComparator:comparator2cnf,
                comparator
               ]).

% -------------------------------
% | Reduce Comparator           |
% -------------------------------
comparatorSimplify(Constr, NewConstr, Changed):-!,
       Constr=bc(_Type,[X1,X2,Y1,Y2]),
       lit2plit(X1,X1l,X1op),!,
       (X1l==1 ->
            NewConstr=none,
            (X1op==1 ->
                 litAsgnTrue(Y1,Changed), litUnify(Y2,X2,Changed) ;
                 litAsgnFalse(Y2,Changed), litUnify(Y1,X2,Changed)) ;
       lit2plit(X2,X2l,X2op),!,
       (X2l==1 ->
            NewConstr=none,
            (X2op==1 ->
                 litAsgnTrue(Y1,Changed), litUnify(Y2,X1,Changed) ;
                 litAsgnFalse(Y2,Changed), litUnify(Y1,X1,Changed)) ;
       (X1l==X2l ->
            NewConstr=none,
            (X1op==X2op ->
                 litUnify(X1,Y1,Changed), litUnify(X2,Y2,Changed) ;
                 litAsgnTrue(Y1,Changed), litAsgnFalse(Y2,Changed)) ;
       ((ground(Y1), Y1 =:= -1) ->
            litAsgnFalse(Y2,Changed), litAsgnFalse(X1,Changed), litAsgnFalse(X2,Changed), NewConstr=none ;
       ((ground(Y2), Y2 =:= 1) ->
            litAsgnTrue(Y1,Changed), litAsgnTrue(X1,Changed), litAsgnTrue(X2,Changed), NewConstr=none ;
       lit2plit(Y1,Y1l,Y1op),!,
       lit2plit(Y2,Y2l,Y2op),!,
       (Y1l==Y2l ->
            NewConstr=none,
            (Y1op==Y2op ->
                 litUnify(X1,Y1,Changed), litUnify(X2,Y2,Changed) ;
                 litAsgnTrue(Y1,Changed), litAsgnFalse(Y2,Changed), litUnify(X1,-X2,Changed)) ;
       NewConstr=Constr
       )))))).

       
comparator2cnf(bc(_,[A, B, C, D]),CnfH-CnfT):-
       ((ground(D), D=:= -1) ->
           CnfH=[[-A, C],[-B, C],[A, B, -C],[-A, -B]|CnfT] ;
       ((ground(C), C=:= 1) ->
           CnfH=[[A, -D],[B, -D],[A, B],[-A, -B, D]|CnfT] ;
       CnfH=[[A, -D],[B, -D],[-A, C],[-B, C],[A, B, -C],[-A, -B, D]|CnfT]
       )).