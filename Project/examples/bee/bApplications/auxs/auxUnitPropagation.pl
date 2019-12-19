:- module('cnfUP', [unitPropogation/2]).

%%% UNIT PROPOGATION
unitprob([[X]|Cs],1):-!,
        litAsgnTrue(X),!,
        unitprob(Cs,_).
unitprob([_|Cs],C):-!,
        unitprob(Cs,C).
unitprob([],_).

unitPropogation(Cnf,Cnf2):-!,
      cnfFixer(Cnf,CnfF),!,
      unitprob(CnfF,CL),!,
      (CL==1 ->
         unitPropogation(CnfF,Cnf2) ;
         Cnf2=CnfF).
                 
                 
clauseFixer([X|Xs],Clause,Keep):-!,
       (ground(X) ->
           (X =:= 1 -> Keep=0 ;
           (X =:= -1 -> clauseFixer(Xs,Clause,Keep) ;
           Z is X, Clause=[Z|MClause], clauseFixer(Xs,MClause,Keep)
           )) ;
       Clause=[X|MClause],
       clauseFixer(Xs,MClause,Keep)
       ).
clauseFixer([],[],1):-!.

cnfFixer([Clause|Clauses],NewClauses):-!,
                clauseFixer(Clause,NewClause, Keep),!,
                (Keep==0 ->
                  cnfFixer(Clauses,NewClauses)
                  ;
                  NewClauses=[NewClause | MNewClauses],
                  cnfFixer(Clauses,MNewClauses)).
cnfFixer([],[]):-!.

litAsgnTrue(X):-X is 1,!.
litAsgnTrue(-(X)):-!,litAsgnFalse(X).

litAsgnFalse(X):-X is -1, !.
litAsgnFalse(-X):-!,litAsgnTrue(X).