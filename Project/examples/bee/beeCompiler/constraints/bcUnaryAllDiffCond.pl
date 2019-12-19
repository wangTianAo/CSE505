% Author: Amit Metodi
% Last Updated: 01/07/2014


:- module(bcUnaryAllDiffCond, [ ]).

:- Head=int_array_allDiffCond(Ints,Conds,ConstrsH-ConstrsT),
   Body=(
       !,
       length(Ints,N),
       length(Conds,N),
       !,
       bcUnaryAllDiffCond:allDiffCondParserDecompose(Ints,Conds,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).
   

allDiffCondParserDecompose([],[],Constrs-Constrs):-!.
allDiffCondParserDecompose([_],[_],Constrs-Constrs):-!.
allDiffCondParserDecompose([X0|Ints],[C0|Conds],ConstrsH-ConstrsT):-!,
   allDiffCondParserDecompose_aux(Ints,Conds,X0,C0,ConstrsH-ConstrsM),!,
   allDiffCondParserDecompose(Ints,Conds,ConstrsM-ConstrsT).

allDiffCondParserDecompose_aux([],[],_,_,Constrs-Constrs):-!.
allDiffCondParserDecompose_aux([X1|Ints],[C1|Conds],X0,C0,ConstrsH-ConstrsT):-!,
   bParser:int_neq_reif(X0,X1,Neq,ConstrsH-ConstrsM1),
   bParser:bool_array_or([-C0, -C1, Neq],ConstrsM1-ConstrsM2),!,
   allDiffCondParserDecompose_aux(Ints,Conds,X0,C0,ConstrsM2-ConstrsT).
