% Author: Amit Metodi
% Last Updated: 05/09/2016

:- module(bcBool, [ ]).

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=new_bool(_,Constrs-Constrs),
   bParser:addConstraint(Head).

:- Head=new_temp_bool(_,Constrs-Constrs),
   bParser:addConstraint(Head).

:- Head=bool_eq(X,Y,Constrs-Constrs),
   Body=(
       !,
       auxLiterals:litUnify(X,Y)
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_array_and(Bs,Constrs-Constrs),
   Body=(
       !,
       auxLiterals:litAsgnTrues(Bs)
   ),
   bParser:addConstraint(Head,Body).
