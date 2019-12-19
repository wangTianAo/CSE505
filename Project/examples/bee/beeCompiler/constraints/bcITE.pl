% Author: Amit Metodi
% Last Updated: 24/08/2016

:- module(bcITE, [ ]).
:- use_module('../auxs/auxLiterals').

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=bool_ite(If,Then,Else,ConstrsH-ConstrsT),
   Body=(
       !,
       bcITE:iteType(ITEType),
       bcITE:iteSimplify(bc(ITEType,[If,Then,Else]),Constr,_),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_ite_reif(If,Then,Else,Reif,ConstrsH-ConstrsT),
   Body=(
       !,
       bcITE:iteReifType(ITEType),
       bcITE:iteReifSimplify(bc(ITEType,[If,Then,Else,Reif]),Constr,_),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
iteType([
        bcITE:iteSimplify,
        skipSimplify,
        0,
        bcITE:ite2cnf,
        ite
       ]):-!.

iteReifType([
        bcITE:iteReifSimplify,
        skipSimplify,
        0,
        bcITE:iteReif2cnf,
        ite
       ]):-!.

% -------------------------------
% | Simplify predicates         |
% -------------------------------
           
iteSimplify(Constr,NewConstr,Changed):-!,
    Constr=bc(_Type,[If,Then,Else]),
    (ground(If) ->
        Changed=1,
        NewConstr=none,
        (If =:= 1 ->
           litAsgnTrue(Then)  %% ( 1 ? Then : Else)
        ;
           litAsgnTrue(Else)  %% (-1 ? Then : Else)
        ) ;
    (ground(Then) ->
        Changed=1,
        (Then =:= -1 ->
            NewConstr=none,  %% (If ? -1 : Else)
            litAsgnTrue(Else),
            litAsgnFalse(If)
        ;
            bcAtLeastOne:aloType(AloType),  %% (If ? 1 : Else)
            lits2plits([If,Else],AloVec),
            bcAtLeastOne:aloSimplify(bc(AloType,AloVec),NewConstr,_)
        ) ;
    (ground(Else) ->
        Changed=1,
        (Else =:= -1 ->
            NewConstr=none,    %% (If ? Then : -1)
            litAsgnTrue(Then),
            litAsgnTrue(If)
        ;
            bcAtLeastOne:aloType(AloType),  %% (If ? Then : 1)
            lits2plits([-If,Then],AloVec),
            bcAtLeastOne:aloSimplify(bc(AloType,AloVec),NewConstr,_)
        ) ;
    lit2plit(Then,Thenl,ThenOp),
    lit2plit(Else,Elsel,ElseOp),
    (Thenl==Elsel ->
        Changed=1,
        NewConstr=none,
        (ThenOp==ElseOp ->
            litAsgnTrue(Then) %% (Z ? X : X)
        ;
            litUnify(If,Then) %% (Z ? X : -X)
        ) ;
    NewConstr=Constr
    )))).

        
        
iteReifSimplify(Constr,NewConstr,Changed):-!,
    Constr=bc(_Type,[If,Then,Else,Reif]),
    (ground(If) ->
        Changed=1,
        NewConstr=none,
        (If =:= 1 ->
            litUnify(Then,Reif)  %% (1 ? Then : Else) == Reif  ->  Then==Reif
        ;
            litUnify(Else,Reif)  %% (-1 ? Then : Else) == Reif  ->  Else==Reif
        ) ;
    (ground(Reif) ->
        Changed=1,
        iteType(ITEType),
        (Reif =:= 1 ->
            iteSimplify(bc(ITEType,[If,Then,Else]),NewConstr,_)  %% (If ? Then : Else) == 1
        ;
            iteSimplify(bc(ITEType,[If,-Then,-Else]),NewConstr,_)  %% (If ? Then : Else) == -1
        ) ;
    lit2plit(Then,Thenl,ThenOp),
    lit2plit(Else,Elsel,ElseOp),
    (Thenl==Elsel ->
        Changed=1,
        (ThenOp==ElseOp ->
            NewConstr=none,  %% (If ? X : X) == Reif  ->  Reif==X
            litUnify(Then,Reif)
        ;
            lits2plits([If,Reif],XorVec),  %% (If ? X : -X) == Reif
            bcXor:xorType(XorType),
            bcXor:xorVecSimplify(bc(XorType,[(Thenl,ThenOp)|XorVec]),NewConstr,_)
        ) ;
    lit2plit(If,Ifl,IfOp),
    lit2plit(Reif,Reifl,ReifOp),
    (Ifl==Reifl ->
        Changed=1,
        iteType(ITEType),
        (IfOp==ReifOp ->
            iteSimplify(bc(ITEType,[If,Then,-Else]),NewConstr,_) % (X ? Then : Else) == X
        ;
            iteSimplify(bc(ITEType,[If,-Then,Else]),NewConstr,_) % (X ? Then : Else) == -X
        ) ;
    (ground(Then) ->
        Changed=1,
        bcOr:orType(OrType),
        (Then =:= 1 ->
            auxLiterals:lits2plits([If,Else],OrVecA),
            OrVec=[Reif|OrVecA]   %%  (If ? 1 : Else) == Reif  -> (If || Else) == Reif
        ;
            auxLiterals:lits2plits([If,-Else],OrVecA),
            OrVec=[-Reif|OrVecA]  %%  (If ? -1 : Else) == Reif  -> (If || -Else) == -Reif
        ),
        bcOr:orSimplify(bc(OrType,OrVec),NewConstr,_) ;
    (ground(Else) ->
        Changed=1,
        bcOr:orType(OrType),
        (Else =:= 1 ->
            auxLiterals:lits2plits([-If,Then],OrVecA),
            OrVec=[Reif|OrVecA]   %%  (If ? Then : 1) == Reif  -> (-If || Then) == Reif
        ;
            auxLiterals:lits2plits([-If,-Then],OrVecA),
            OrVec=[-Reif|OrVecA]  %%  (If ? Then : -1) == Reif  -> (-If || -Then) == -Reif
        ),
        bcOr:orSimplify(bc(OrType,OrVec),NewConstr,_) ;
    NewConstr=Constr
    )))))).

% -------------------------------
% | Encode predicates           |
% -------------------------------

ite2cnf(bc(_,[If,Then,Else]),CnfH-CnfT):-!,
    CnfH=[
          [-If, Then],
          [ If, Else],
          [Then,Else] %% redundent clause for better propagation
          |CnfT].

iteReif2cnf(bc(_,[If,Then,Else,Reif]),CnfH-CnfT):-!,
    CnfH=[
          [-If, -Then,  Reif],
          [-If,  Then, -Reif],
          [ If,  Else, -Reif],
          [ If, -Else,  Reif],
          [ Then,  Else, -Reif], %% redundent clause for better propagation
          [-Then, -Else,  Reif]  %% redundent clause for better propagation
          |CnfT].
