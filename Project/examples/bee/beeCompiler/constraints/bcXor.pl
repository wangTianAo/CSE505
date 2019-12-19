% Author: Amit Metodi
% Last Updated: 13/04/2012

:- module(bcXor, [ ]).
:- use_module('../auxs/auxLiterals').
%:- use_module('../auxs/xorVec').

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=bool_array_xor(Bs,ConstrsH-ConstrsT),
   Body=(
       !,
       bcXor:xorType(Type),
       auxLiterals:lits2plits(Bs,Vec),
       bcXor:xorVecSimplify(bc(Type,Vec),Constr,_),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_array_xor_reif(Bs,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcXor:xorType(Type),
       auxLiterals:lits2plits([-Z|Bs],Vec),
       bcXor:xorVecSimplify(bc(Type,Vec),Constr,_),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_xor_reif(A,B,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcXor:xorType(Type),
       auxLiterals:lits2plits([A,B,-Z],Vec),
       bcXor:xorVecSimplify(bc(Type,Vec),Constr,_),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).


:- Head=bool_array_iff(Bs,ConstrsH-ConstrsT),
   Body=(
       !,
       bcXor:xorType(Type),
       (Bs=[B|RBs] ->
          auxLiterals:lits2plits([-B|RBs],Vec)
       ;
          Bs=[], Vec=[(1,1)]
       ),
       bcXor:xorVecSimplify(bc(Type,Vec),Constr,_),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_array_iff_reif(Bs,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcXor:xorType(Type),
       auxLiterals:lits2plits([Z|Bs],Vec),
       bcXor:xorVecSimplify(bc(Type,Vec),Constr,_),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_iff_reif(A,B,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bcXor:xorType(Type),
       auxLiterals:lits2plits([A,B,Z],Vec),
       bcXor:xorVecSimplify(bc(Type,Vec),Constr,_),
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
xorType([
         bcXor:xorVecSimplify,
         skipSimplify,
         0,
         bcXor:xorVec2cnf,
         xor]):-!.


%%% X1 + X2 + .. + Xn <-> Z
%%% XorVec=[X1,X2,..,Xn,-Z]
%%% sum(XorVec) mod 2 = 1
xorVecSimplify(Constr,NewConstr,Changed):-!,
    Constr=bc(Type,XorVec),
    xorVec:xorSimplify(XorVec,NXorVec,Changed),
    (NXorVec=[] -> throw(unsat) ;
    (NXorVec=[PBit] ->
        NewConstr=none,
        Changed=1,
        plitAsgnTrue(PBit) ;
    (NXorVec=[PBit1,PBit2] ->
        NewConstr=none,
        Changed=1,
        plitUnifyDiff(PBit1,PBit2) ;
    (Changed==1 ->
        NewConstr=bc(Type,NXorVec)
    ;
        NewConstr=Constr
    )))).


:- if(bSettings:useXorClauses(true)).

%%% CryptoMinisat support
xorVec2cnf(bc(_Type,XorVec),[[x|Vec]|CnfT]-CnfT):-!,
       plits2lits(XorVec,Vec).

:- else.

xorVec2cnf(bc(_Type,XorVec),CnfH-CnfT):-!,
    plits2lits(XorVec,[Z|BitVec]),
    xor2cnf(BitVec,-Z,CnfH-CnfT).

xor2cnf([X,Y],Z,CnfH-CnfT):-!,
    CnfH=[[-X, Y, Z],
          [ X,-Y, Z],
          [ X, Y,-Z],
          [-X,-Y,-Z]
          |CnfT].
xor2cnf([Q,X,Y],Z,CnfH-CnfT):-!,
    xor2cnf([Q,X],T,CnfH-CnfM),
    xor2cnf([T,Y],Z,CnfM-CnfT).
xor2cnf(Vec,Z,CnfH-CnfT):-!,
    auxLists:listOddEvenSplit(Vec,Vec1,Vec2),
    xor2cnf(Vec1,T1,CnfH-CnfM1),
    xor2cnf(Vec2,T2,CnfM1-CnfM2),
    xor2cnf([T1,T2],Z,CnfM2-CnfT).

:- endif.