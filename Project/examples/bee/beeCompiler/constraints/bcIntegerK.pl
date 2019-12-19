% Author: Amit Metodi
% Last Updated: 22/04/2017

:- module(bcIntegerInc, [ ]).

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=new_int_plusK(New,Old,K,Constrs-Constrs),
   Body=(
        (integer(K) ->
        (var(New) ->
            bcInteger:getUnaryNumber(Old,OldU),!,
			auxUnarynum:unarynumAddConst(OldU,K,(Amin,Amax,Aunary)),!,
            New=(int,Amin,Amax,[(order,Aunary)]) ;
        throw(model_err(new_int_plusK,'the variable was already defined !'))) ;
        throw(model_err(new_int_plusK,'3rd parameter is not a constant !')))
   ),
   bParser:addConstraint(Head,Body).

:- Head=new_int_direct_plusK(New,Old,K,Constrs-Constrs),
   Body=(
        (integer(K) ->
        (var(New) ->
            bcInteger:getDirectNumber(Old,(Amin,Amax,Adirect)),!,
            Bmin is Amin + K,
            Bmax is Amax + K,
            New=(int,Bmin,Bmax,[(direct,Adirect)]) ;
        throw(model_err(new_int_direct_plusK,'the variable was already defined !'))) ;
        throw(model_err(new_int_direct_plusK,'3rd parameter is not a constant !')))
   ),
   bParser:addConstraint(Head,Body).

:- Head=new_int_dual_plusK(New,Old,K,Constrs-Constrs),
   Body=(
        (integer(K) ->
        (var(New) ->
            bcInteger:getUnaryNumber(Old,(Amin,Amax,Aunary)),!,
            bcInteger:getDirectNumber(Old,(Amin,Amax,Adirect)),!,
            Bmin is Amin + K,
            Bmax is Amax + K,
            New=(int,Bmin,Bmax,[(order,Aunary),(direct,Adirect)]) ;
        throw(model_err(new_int_direct_plusK,'the variable was already defined !'))) ;
        throw(model_err(new_int_direct_plusK,'3rd parameter is not a constant !')))
   ),
   bParser:addConstraint(Head,Body).

   
:- Head=new_int_mulK(New,Old,K,Constrs-Constrs),
   Body=(
        (integer(K) ->
        (var(New) ->
            bcInteger:getUnaryNumber(Old,OldU),!,
			auxUnarynum:unarynumMulByConst(OldU,K,(Amin,Amax,Aunary)),!,
            New=(int,Amin,Amax,[(order,Aunary)]) ;
        throw(model_err(new_int_mulK,'the variable was already defined !'))) ;
        throw(model_err(new_int_mulK,'3rd parameter is not a constant !')))
   ),
   bParser:addConstraint(Head,Body).

:- Head=new_int_divK(New,Old,K,Constrs-Constrs),
   Body=(
        (integer(K) ->
        (var(New) ->
            bcInteger:getUnaryNumber(Old,OldU),!,
			auxUnarynum:unarynumDivByConst(OldU,K,(Amin,Amax,Aunary)),!,
            New=(int,Amin,Amax,[(order,Aunary)]) ;
        throw(model_err(new_int_mulK,'the variable was already defined !'))) ;
        throw(model_err(new_int_mulK,'3rd parameter is not a constant !')))
   ),
   bParser:addConstraint(Head,Body).
   
  