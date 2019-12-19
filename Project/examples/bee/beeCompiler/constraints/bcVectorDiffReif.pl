% Author: Amit Metodi
% Last Updated: 20/09/2015

:- module(bcVectorDiffReif, [ ]).
:- use_module('../auxs/auxLiterals').


:- Head=bool_arrays_eq(A,B,Constrs-Constrs),
   Body=(
         !,
         auxLiterals:litUnifiesWfalses(A,B)
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_arrays_neq(A,B,[bc(Type,[A,B])|Constrs]-Constrs),
   Body=(
       !,
         bcVectorDiffReif:vectorsDiffType(Type)
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_arrays_eq_reif(A,B,Z,ConstrsH-ConstrsT),
   Body=(
         !,
         bParser:bool_arrays_neq_reif(A,B,-Z,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_arrays_neq_reif(A,B,Z,[bc(Type,[A,B,Z])|Constrs]-Constrs),
   Body=(
       !,
         bcVectorDiffReif:vectorsDiffReifType(Type)
   ),
   bParser:addConstraint(Head,Body).


%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
:- if(bSettings:vectorDiff(decompose)).

vectorsDiffType([
                   bcVectorDiffReif:vectorsDiffSimplify,
                   skipSimplify,
                   bcVectorDiffReif:vectorsDiffDecompose,
                   0,
                   vectorsDiff]).

vectorsDiffReifType([
                   bcVectorDiffReif:vectorsDiffReifSimplify,
                   skipSimplify,
                   bcVectorDiffReif:vectorsDiffReifDecompose,
                   0,
                   vectorsDiffReif]).

:- else.

vectorsDiffType([
                   bcVectorDiffReif:vectorsDiffSimplify,
                   skipSimplify,
                   0,
                   bcVectorDiffReif:vectorsDiff2cnf,
                   vectorsDiff]).

vectorsDiffReifType([
                   bcVectorDiffReif:vectorsDiffReifSimplify,
                   skipSimplify,
                   0,
                   bcVectorDiffReif:vectorsDiffReif2cnf,
                   vectorsDiffReif]).

:- endif.

% --------------------------------
% | Simplify (A != B)            |
% --------------------------------
vectorsDiffSimplify(Constr, NewConstr, Changed):-!,
    Constr=bc(Type,[As,Bs]),
     vecDIFFvecReduce(As,Bs,NAs,NBs,AdiffB,Changed),
     (AdiffB == 1 ->
           Changed=1,
           NewConstr=none ;
     (NAs=[] ->
           throw(unsat) ;
     (NAs=[A] ->
            Changed=1,
            NBs=[B],
            litUnify(A,-B),
            NewConstr=none ;
     (Changed == 1 ->
         NewConstr=bc(Type,[NAs,NBs])
     ;
         NewConstr = Constr
     )))).

vecDIFFvecReduce([A|As],[B|Bs],NAs,NBs,AdiffB,Changed):-
     (litIsEqual(A,-B) ->
        Changed=1,
        AdiffB=1 ;
     (litIsEqual(A,B) ->
        Changed=1,
        vecDIFFvecReduce(As,Bs,NAs,NBs,AdiffB,Changed) ;
     NAs=[A|NNAs],
     NBs=[B|NNBs],
     vecDIFFvecReduce(As,Bs,NNAs,NNBs,AdiffB,Changed)
     )).
vecDIFFvecReduce([],[],[],[],_,_).

vecDIFFvecReduce([A|As],[],NAs,NBs,AdiffB,1):-!,
    vecDIFFvecReduce([A|As],[-1],NAs,NBs,AdiffB,_).
vecDIFFvecReduce([],[B|Bs],NAs,NBs,AdiffB,1):-!,
    vecDIFFvecReduce([-1],[B|Bs],NAs,NBs,AdiffB,_).


% --------------------------------
% | Simplify (A != B)<->Z        |
% --------------------------------
vectorsDiffReifSimplify(Constr, NewConstr, Changed):-!,
    Constr=bc(Type,[As,Bs,Z]),
    (ground(Z) ->
        Changed=1,
        (Z =:= -1 ->  % A==B
            litUnifiesWfalses(As,Bs),
            NewConstr=none
        ;
            vectorsDiffType(DiffType),
            vectorsDiffSimplify(bc(DiffType,[As,Bs]),NewConstr, _)
        )
    ;
        vecDIFFvecReduce(As,Bs,NAs,NBs,AdiffB,Changed),
        (AdiffB==1 ->
            Changed=1,
            litAsgnTrue(Z),
            NewConstr=none ;
        (NAs=[] ->
            Changed=1,
            litAsgnFalse(Z),
            NewConstr=none ;
        (NAs=[A] ->
            NBs=[B],
            Changed=1,
            bcXor:xorType(XorType),
            auxLiterals:lits2plits([A,B,-Z],Vec),
            bcXor:xorVecSimplify(bc(XorType,Vec),NewConstr,_) ;
        (Changed == 1 ->
            NewConstr=bc(Type,[NAs,NBs,Z])
        ;
            NewConstr = Constr
     ))))).

% --------------------------------
% | Decompose                    |
% --------------------------------

vectorsDiffDecompose(Constr, Constraints):-!,
    Constr=bc(_,[As,Bs]),
    auxLiterals:lits2plits(As,PAs),
    auxLiterals:lits2plits(Bs,PBs),
    bcXor:xorType(XorType),
    xorVectors(PAs,PBs,PDs,XorType,Constraints-Cs),
    bcAtLeastOne:aloType(ALOType),
    Cs=[bc(ALOType,PDs)].

vectorsDiffReifDecompose(Constr, Constraints):-!,
    Constr=bc(_,[As,Bs,Z]),
    auxLiterals:lits2plits(As,PAs),
    auxLiterals:lits2plits(Bs,PBs),
    bcXor:xorType(XorType),
    xorVectors(PAs,PBs,PDs,XorType,Constraints-Cs),
    bcOr:orType(OrType),
    Cs=[bc(OrType,[Z|PDs])].


xorVectors([A|As],[B|Bs],[D|Ds],XorType,[bc(XorType,[ND,A,B])|CsH]-CsT):-!,
    D=(Dl,1),
    ND=(Dl,-1),
    xorVectors(As,Bs,Ds,XorType,CsH-CsT).
xorVectors([],[],[],_,Cs-Cs):-!.



% --------------------------------
% | Encode                       |
% --------------------------------

vectorsDiff2cnf(bc(_,[As,Bs]), CnfH-CnfT):-!,
   implyVectorEqReif(As,Bs,1,-1,CnfH-CnfT).

vectorsDiffReif2cnf(bc(_,[As,Bs,Z]), CnfH-CnfT):-!,
   implyVectorEqReif(As,Bs,1,-Z,CnfH-CnfT).


%% Encode:  (Imp => ((A==B)<=>Rief)) && (!Imp=>!Reif))
implyVectorEqReif([A|As],[B|Bs],Imp,FReif,CnfH-CnfT):-!,
   CnfH=[[Imp,-CReif],       %% !Imp => !Reif
         [-Imp,A,B,CReif],   %% Imp && (A==B) => Reif
         [-Imp,-A,-B,CReif], %% Imp && (A==B) => Reif
         [-A,B,-CReif],      %% (A!=B) => !Reif
         [A,-B,-CReif]       %% (A!=B) => !Reif
         |CnfM],
   implyVectorEqReif(As,Bs,CReif,FReif,CnfM-CnfT).
implyVectorEqReif([],[],Reif,Reif,Cnf-Cnf):-!.
implyVectorEqReif([A|As],[],Imp,FReif,CnfH-CnfT):-!,
   CnfH=[[Imp,-CReif],     %% !Imp => !Reif
         [-Imp,A,CReif],   %% Imp && (A==B) => Reif
         [-A,-CReif]       %% (A!=B) => !Reif
         |CnfM],
   implyVectorEqReif(As,[],CReif,FReif,CnfM-CnfT).
implyVectorEqReif([],[B|Bs],Imp,FReif,CnfH-CnfT):-!,
   CnfH=[[Imp,-CReif],     %% !Imp => !Reif
         [-Imp,B,CReif],   %% Imp && (A==B) => Reif
         [-B,-CReif]       %% (A!=B) => !Reif
         |CnfM],
   implyVectorEqReif([],Bs,CReif,FReif,CnfM-CnfT).