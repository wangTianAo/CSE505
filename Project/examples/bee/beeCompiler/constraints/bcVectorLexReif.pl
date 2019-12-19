% Author: Amit Metodi
% Last Updated: 08/06/2013

:- module(bcVectorLexReif, [ ]).
:- use_module('../auxs/auxLiterals').

:- Head=bool_arrays_lex_reif(A,B,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcVectorLexReif:vectorsLEqReifType(Type),
       bcVectorLexReif:vectorLEqReifSimplify(bc(Type,[Z,A,B]),Constr,_),
       (Constr==none ->
            ConstrsH=ConstrsT
       ;
            ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_arrays_lexLt_reif(A,B,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bParser:bool_arrays_lex_reif(B,A,-Z,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
vectorsLEqReifType([
              bcVectorLexReif:vectorLEqReifSimplify,
              skipSimplify,
              0,
              bcVectorLexReif:vectorLEqReif2cnf,
              vectorLexReif
             ]).

% --------------------------------
% | Simplify (A <= B)<->Z        |
% --------------------------------
vectorLEqReifSimplify(Constr, NewConstr, Changed):-!,
    Constr=bc(Type,[Z,A,B]),
    (ground(Z) ->
        Changed=1,
        bcVectorLex:vectorsLEqType(NewType),
        (Z =:= 1 ->
            bcVectorLex:vectorLEqSimplify(bc(NewType,[A,B]), NewConstr, _)
        ;
            bcVectorLex:vectorsLexLt2Lex(B,A,FB,FA),
            bcVectorLex:vectorLEqSimplify(bc(NewType,[FB,FA]), NewConstr, _)
        )
    ;
        vecLEqVecReif_sim(A,B,NA,NB,Changed),
        ((NA=[], NB=[]) ->
            Changed=1,
            litAsgnTrue(Z),
            NewConstr=none
        ;
        ((NA=[A0], NB=[B0]) ->
            Changed=1,
            bcOr:orType(OrType),
            auxLiterals:lits2plits([B0,-A0],OrVec),
            bcOr:orSimplify(bc(OrType,[Z|OrVec]),NewConstr,_)
        ;
        (Changed==1 ->
            NewConstr=bc(Type,[Z,NA,NB])
        ;
            NewConstr=Constr
        )))
    ).


vecLEqVecReif_sim([A|As],[B|Bs],NAs,NBs,Changed):-!,
    lit2plit(A,Al,AOp),
    lit2plit(B,Bl,BOp),
    (Al==Bl ->
        (AOp==BOp ->
            Changed=1,
            vecLEqVecReif_sim(As,Bs,NAs,NBs,_)
        ;
            ((ground(Bl), B=:=1) ->
                Changed=1,
                NAs=[],
                NBs=[]
            ;
                NAs=[A],
                NBs=[B],
                ((As=[], Bs=[]) ; Changed=1)
            )
        )
    ;
        NAs=[A|MAs],
        NBs=[B|MBs],
        vecLEqVecReif_sim(As,Bs,MAs,MBs,Changed)
    ).
vecLEqVecReif_sim([],[],[],[],_):-!.
vecLEqVecReif_sim([],[B|Bs],NAs,NBs,Changed):-!,
    vecLEqVecReif_sim([-1],[B|Bs],NAs,NBs,Changed).
vecLEqVecReif_sim([A|As],[],NAs,NBs,Changed):-!,
    vecLEqVecReif_sim([A|As],[-1],NAs,NBs,Changed).


% --------------------------------
% | CNF                          |
% --------------------------------
vectorLEqReif2cnf(bc(_,[Z,As,Bs]),CnfH-CnfT):-
    vecLEqvecReifCnf(As,Bs,Z,CnfH-CnfT).

:- if(bSettings:useXorClauses(true)).
vecLEqvecReifCnf([Ai|As],[Bi|Bs],Z,CnfH-CnfT):-!,
        CnfH=[
              [x,Ai,Bi,CurEq],
              [-Ai,Bi,-Z],     % Ai=1 & Bi=0 -> -Z
              [Ai,-Bi,Z]       % Ai=0 & Bi=1 -> Z
              |CnfM],
        vecLEqvecReifCnf_(As,Bs,CurEq,Z,CnfM-CnfT).
:- else.
vecLEqvecReifCnf([Ai|As],[Bi|Bs],Z,CnfH-CnfT):-!,
        CnfH=[
              [Ai,Bi,CurEq],   % PrevEq & Ai=Bi=0 -> CurEq
              [-Ai,-Bi,CurEq], % PrevEq & Ai=Bi=1 -> CurEq
              [Ai,-Bi,-CurEq], % Ai=0 & Bi=1 -> -CurEq
              [-Ai,Bi,-CurEq], % Ai=1 & Bi=0 -> -CurEq
              [-Ai,Bi,-Z],     % Ai=1 & Bi=0 -> -Z
              [Ai,-Bi,Z]       % Ai=0 & Bi=1 -> Z
              |CnfM],
        vecLEqvecReifCnf_(As,Bs,CurEq,Z,CnfM-CnfT).
:- endif.

vecLEqvecReifCnf_([Ai],[Bi],PrevEq,Z,CnfH-CnfT):-!,
        CnfH=[
              [-PrevEq,Ai,Z],      % PrevEq & Ai=0 -> Z
              [-PrevEq,-Bi,Z],     % PrevEq & Bi=1 -> Z
              [-PrevEq,-Ai,Bi,-Z]  % PrevEq & Ai=1 & Bi=0 -> -Z
              |CnfT].
vecLEqvecReifCnf_([Ai|As],[Bi|Bs],PrevEq,Z,CnfH-CnfT):-!,
        CnfH=[
              [PrevEq, -CurEq],        % -PrevEq -> -CurEq
              [-PrevEq,Ai,Bi,CurEq],   % PrevEq & Ai=Bi=0 -> CurEq
              [-PrevEq,-Ai,-Bi,CurEq], % PrevEq & Ai=Bi=1 -> CurEq
              [Ai,-Bi,-CurEq],         % Ai=0 & Bi=1 -> -CurEq
              [-Ai,Bi,-CurEq],         % Ai=1 & Bi=0 -> -CurEq
              [-PrevEq,-Ai,Bi,-Z],     % Ai=1 & Bi=0 -> -Z
              [-PrevEq,Ai,-Bi,Z]       % Ai=0 & Bi=1 -> Z
              |CnfM],
        vecLEqvecReifCnf_(As,Bs,CurEq,Z,CnfM-CnfT).
