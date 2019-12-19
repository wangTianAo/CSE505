% Author: Amit Metodi
% Last Updated: 05/03/2012

:- module(bParser, [parse/2]).

parse([Constr|Input],OutConstrH-OutConstrT):-!,
    %call(Constr,OutConstrH-OutConstrM),!,
    (
     catch(
         call(Constr,OutConstrH-OutConstrM),
         error(existence_error(_,_CallConstr),_),
         (Constr =.. [ConstrName|_] , throw(unsupported(ConstrName)))
          )
    ;
     (Constr =.. [Name|Args], throw(bug(parse,bc([_,_,_,_,Name],Args))))
    ),!,
    parse(Input,OutConstrM-OutConstrT).
parse([],OutConstr-OutConstr):-!.

addConstraint(Head,Body):-
    dynamic(Head),
    assertz(Head :- Body),
    compile_predicates([Head]).
addConstraint(Head):-
    dynamic(Head),
    assertz(Head),
    compile_predicates([Head]).
