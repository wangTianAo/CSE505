% Author: Amit Metodi
% Last Updated: 29/09/2015

:- module(bcUnaryDiffReif, [ ]).
:- use_module('../auxs/auxLiterals').


:- Head=int_neq_reif(A,B,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       (ground(Z) ->
           (Z=:=1 ->
               bParser:int_neq(A,B,ConstrsH-ConstrsT)
           ;
               bParser:int_eq(A,B,ConstrsH-ConstrsT)
           ) ;
       bcInteger:getUnaryNumber(A,Au),
       auxUnarynum:unarynumIsChangedOrConst(Au,FA,_),
       bcInteger:getUnaryNumber(B,Bu),
       auxUnarynum:unarynumIsChangedOrConst(Bu,FB,_),!,
       ((FA=(Ac,Ac,_), bcInteger:haveDirectNumber(B)) ->
           bcInteger:getDirectNumber(B,Bd),
           bcUnaryDiffReif:unaryDiffReifSimplifyDirect(Ac,Bd,Z),
           ConstrsH=ConstrsT
       ;
       ((FB=(Bc,Bc,_), bcInteger:haveDirectNumber(A)) ->
           bcInteger:getDirectNumber(A,Ad),
           bcUnaryDiffReif:unaryDiffReifSimplifyDirect(Bc,Ad,Z),
           ConstrsH=ConstrsT
       ;
       bcUnaryDiffReif:unaryDiffReifType(Type),
       bcUnaryDiffReif:unaryDiffReifSimplify(bc(Type,[Z,FA,FB]),Constr, 1),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       ))))
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_eq_reif(A,B,Z,ConstrsH-ConstrsT),
   Body=(
       !,
       bParser:int_neq_reif(A,B,-Z,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).


%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
unaryDiffReifType([
                   bcUnaryDiffReif:unaryDiffReifSimplify,
                   bcUnaryDiffReif:unaryDiffReifSimplifyAdv,
                   0,
                   bcUnaryDiffReif:unaryDiffReif2cnf,
                   unaryDiffReif]).

unaryDiffKReifType([
                   bcUnaryDiffReif:unaryDiff1ReifSimplify,
                   skipSimplify,
                   0,
                   bcUnaryDiffReif:unaryDiff1Reif2cnf,
                   unaryDiffKReif]).


unaryDiffReifSimplifyDirect(K,(Min,Max,Bits,_),Z):-
    (K < Min -> litAsgnTrue(Z) ;
    (K > Max -> litAsgnTrue(Z) ;
    Drop is K - Min,
    auxLists:listDropFrom(Drop,Bits,[NZ|_]),
    litUnify(Z,-NZ)
    )).


% --------------------------
% | Simplify Z = (A != B)  |
% --------------------------
unaryDiffReifSimplify(Constr,NewConstr, Changed):-!,
    Constr=bc(Type,[Z,A,B]),
    (ground(Z) ->
        Changed=1,
        (Z =:= 1 ->
             bcUnaryDiff:unaryDiffType(DiffType),
             bcUnaryDiff:unaryDiffSimplify(bc(DiffType,[A,B]),NewConstr, 1)
        ;
             NewConstr=none,
             auxUnarynum:unarynumEquals(A,B)
        ) ;
    auxUnarynum:unarynumIsChangedOrConst(A,FA,Changed),
    auxUnarynum:unarynumIsChangedOrConst(B,FB,Changed),!,
    (Changed==1 ->
        FA=(Amin,Amax,_),
        FB=(Bmin,Bmax,_),
        ((Amin > Bmax ; Amax < Bmin) ->
            litAsgnTrue(Z),
            NewConstr=none ;
        (Amin==Amax ->
            change2diffK(FB,Amin,Z,NewConstr) ;
        (Bmin==Bmax ->
            change2diffK(FA,Bmin,Z,NewConstr) ;
        (Amin==Bmax ->
            FA=(_,_,[Ab|_],_),
            FB=(_,_,_,Bb),
            bcOr:orType(OrType),
            auxLiterals:lits2plits([Ab,-Bb],OrVec),
            bcOr:orSimplify(bc(OrType,[Z|OrVec]),NewConstr,_) ;
        (Amax==Bmin->
            FB=(_,_,[Bb|_],_),
            FA=(_,_,_,Ab),
            bcOr:orType(OrType),
            auxLiterals:lits2plits([-Ab,Bb],OrVec),
            bcOr:orSimplify(bc(OrType,[Z|OrVec]),NewConstr,_) ;
        (Amin==Bmin ->
            Dmin=Amin
            ;
            Dmin is max(Amin,Bmin) - 1
        ),
        (Amax==Bmax ->
            Dmax=Amax
        ;
            Dmax is min(Amax,Bmax) + 1
        ),
        auxUnarynum:unarynumFocusOn(FA,Dmin,Dmax,NA),
        auxUnarynum:unarynumFocusOn(FB,Dmin,Dmax,NB),
        NewConstr=bc(Type,[Z,NA,NB])
        )))))
    ;
        NewConstr=Constr
    )).


change2diffK((Min,Max,Bits,LBit),K,Z,Constr):-
    (Max==K ->
        litUnify(Z,-LBit),
        Constr=none ;
    (Min==K ->
        Bits=[FBit|_],
        litUnify(Z,FBit),
        Constr=none ;
    Drop is K - Min - 1,
    auxLists:listDropFrom(Drop,Bits,[A,B|_]),
    unaryDiffKReifType(Type),
    unaryDiff1ReifSimplify(bc(Type,[Z,A,B]),Constr,_)
    )).

% ---------------------------------
% | Reduce Z = (U1 != U2)         |
% ---------------------------------
unaryDiffReifSimplifyAdv(Constr,NewConstr, Changed):-!,
    Constr=bc(Type,[Z,A,B]),
    auxUnarynum:unarynumIsChangedOrConst(A,FA,Changed),
    auxUnarynum:unarynumIsChangedOrConst(B,FB,Changed),!,
    (Changed==1 ->
        unaryDiffReifSimplify(bc(Type,[Z,FA,FB]),NewConstr, 1) ;
    A=(Os1,_,Abits,_),
    B=(Os2,_,Bbits,_),
    (Os1==Os2 ->
        reduceZisDiffUnry_s1(Abits,Bbits,NAbits,NBbits,Changed,Zval) ;
    (Os1>Os2 ->
        reduceZisDiffUnry_s1([1|Abits],Bbits,NAbits,NBbits,Changed,Zval) ;
        reduceZisDiffUnry_s1(Abits,[1|Bbits],NAbits,NBbits,Changed,Zval)
    )),!,
    (Zval=lit(NZ) ->
         Changed=1,
         NewConstr=none,
         litUnify(Z,NZ) ;
    (Zval=notOne(X,Y) ->
         Changed=1,
         unaryDiffKReifType(DiffType),
         NewConstr=bc(DiffType,[Z,X,Y]) ;
    (NAbits=[] ->
         Changed=1,
         NewConstr=none,
         litAsgnFalse(Z) ;
    ((NAbits=[X],NBbits=[Y]) ->
         Changed=1,
         auxLiterals:lits2plits([X,Y,-Z],XorVec),
         bcXor:xorType(XorType),
         NewConstr=bc(XorType,XorVec) ;
    (Changed==1 ->
        auxUnarynum:unarynumFromList(NAbits,NA),
        auxUnarynum:unarynumFromList(NBbits,NB),
        unaryDiffReifSimplify(bc(Type,[Z,NA,NB]),NewConstr, 1)
    ;
        NewConstr=Constr
    )))))).


reduceZisDiffUnry_s1([U1|Us1],[U2|Us2], NUs1, NUs2, Changed, Zval):-!,
    lit2plit(U1,U1l,U1op),
    ((U1l==1, U1op== -1) -> Zval=lit(U2) ;
    lit2plit(U2,U2l,U2op),!,
    ((U2l==1, U2op== -1) -> Zval=lit(U1) ;
    (U1l==U2l ->
         (U1op==U2op ->
               Changed=1,
               reduceZisDiffUnry_s1(Us1,Us2, NUs1, NUs2, _,Zval) ;
               Zval=lit(1)) ;
    reduceZisDiffUnry_s2(Us1,(U1,U1l,U1op),Us2,(U2,U2l,U2op),NUs1, NUs2, Changed, Zval)
    ))).
reduceZisDiffUnry_s1([],[], _, _, _, lit(-1)):-!.
reduceZisDiffUnry_s1([A|_],[], _, _, _, lit(A)):-!.
reduceZisDiffUnry_s1([],[B|_], _, _, _, lit(B)):-!.

reduceZisDiffUnry_s2([U12|Us1],(U11,U11l,U11op),[U22|Us2],(U21,U21l,U21op),NUs1, NUs2, Changed, Zval):-!,
    lit2plit(U12,U12l,U12op),!,
    ((U11l==U12l , U11op \== U12op) -> % U1=[A,-A] => U2=[B,B]
          Zval= notOne(U21,U22) ;
    lit2plit(U22,U22l,U22op),!,
    ((U21l==U22l , U21op \== U22op) -> % U2=[A,-A] => U1=[B,B]
          Zval= notOne(U11,U12) ;
    ((U12l == U22l , U12op \== U22op) -> % [?,A,?],[?,-A,?] => diff
          Zval=lit(1) ;

    ((U11l==U22l, U21l==U12l) ->
          ((U11op\==U22op, U21op\==U12op) -> % [A,B],[-B,-A] -> [A,A],[-A,-A]
                Zval= notOne(U11,U12) ;
          ((U11op==U22op, U21op\==U12op) -> % [A,B],[-B,A] -> [A,0],[1,A]
                litAsgnFalse(U12,Changed),
                Zval=lit(1) ;
          ((U11op\==U22op, U21op==U12op) -> % [A,B],[B,-A] -> [1,B],[B,0]
                litAsgnTrue(U11,Changed),
                Zval=lit(1) ;
%          ((U11op==U22op, U21op==U12op) -> % [A,B],[B,A] -> [A,A],[A,A]
                litUnify(U11,U12,Changed),
                lit2plit(U11,U12lF,U12opF),
                reduceZisDiffUnry_s2(Us1,(U11,U12lF,U12opF),Us2,(U11,U12lF,U12opF), NUs1, NUs2, Changed, Zval)
          ))) ;


    (U12l==U22l -> % [?,A,?],[?,A,?] => [?,?],[?,?]
          Changed=1,
          reduceZisDiffUnry_s2(Us1,(U11,U11l,U11op),Us2,(U21,U21l,U21op),NUs1, NUs2, _, Zval) ;

    (U12l==1 ->
          (U12op== -1 ->   % [?,0,?],[?,A,?] => [?,0],[?,A]
               NUs1=[U11,-1],
               NUs2=[U21,U22],
               Zval=keep
          ;                % [?,1,?],[?,A,?] => [1,?],[A,?]
               reduceZisDiffUnry_s2(Us1,(1,1,+),Us2,(U22,U22l,U22op),NUs1, NUs2, _,Zval)
          ) ;

    (U22l==1 ->
          (U22op== -1 ->   % [?,A,?],[?,0,?] => [?,A],[?,0]
               NUs2=[U21,-1],
               NUs1=[U11,U12],
               Zval=keep
          ;                % [?,A,?],[?,1,?] => [A,?],[1,?]
               reduceZisDiffUnry_s2(Us1,(U12,U12l,U12op),Us2,(1,1,+),NUs1, NUs2, _,Zval)
          ) ;
    ((U11l==U12l,U21l==U22l) -> % [A,A],[B,B] => [A],[B]
          Changed=1,
          reduceZisDiffUnry_s2(Us1,(U11,U11l,U11op),Us2,(U21,U21l,U21op),NUs1, NUs2, _,Zval) ;
    NUs1=[U11|NNUs1],
    NUs2=[U21|NNUs2],
    reduceZisDiffUnry_s2(Us1,(U12,U12l,U12op),Us2,(U22,U22l,U22op), NNUs1, NNUs2, Changed, Zval)
    )))))))).
reduceZisDiffUnry_s2([],(U1,_,_),[],(U2,_,_),[U1],[U2],_,keep):-!.
reduceZisDiffUnry_s2([U12|_],(U11,U11l,U11op),[],(U21,U21l,U21op),NUs1, NUs2, Changed, Zval):-!,
    reduceZisDiffUnry_s2([U12],(U11,U11l,U11op),[-1],(U21,U21l,U21op),NUs1, NUs2, Changed, Zval).
reduceZisDiffUnry_s2([],(U11,U11l,U11op),[U22],(U21,U21l,U21op),NUs1, NUs2, Changed, Zval):-!,
    reduceZisDiffUnry_s2([-1],(U11,U11l,U11op),[U22],(U21,U21l,U21op),NUs1, NUs2, Changed, Zval).


% --------------------------------
% | Encode  Z<->(A!=B)           |
% --------------------------------
unaryDiffReif2cnf(bc(_Type,[Z,A,B]),CnfH-CnfT):-
    A=(Amin,_,Abits,_),
    B=(Bmin,_,Bbits,_),
    (Amin==Bmin ->
        unaryDiffCnf(Abits,Bbits,LEq,GEq,Z,CnfH-CnfM) ;
    (Amin>Bmin ->
        Bbits=[B0|MBbits],
        CnfH=[[B0,Z],
              [B0,GEq]
              |Cnf2],
        unaryDiffCnf_aux(Abits,MBbits,1,B0,LEq,GEq,Z,Cnf2-CnfM) ;
    % Amin<Bmin
        Abits=[A0|MAbits],
        CnfH=[[A0,Z],
              [A0,LEq]
              |Cnf2],
        unaryDiffCnf_aux(MAbits,Bbits,A0,1,LEq,GEq,Z,Cnf2-CnfM)
    )),!,
    CnfM=[[LEq,Z],
          [GEq,Z],
          [-LEq,-GEq,-Z]
          |CnfT].

unaryDiffCnf([A|As],[B|Bs],LEq,GEq,Diff,CnfH-CnfT):-!,
    CnfH=[[A,-B,Diff],
          [-A,B,Diff],
          [B,GEq],
          [A,LEq]
          |CnfM],
    unaryDiffCnf_aux(As,Bs,A,B,LEq,GEq,Diff,CnfM-CnfT).

unaryDiffCnf_aux([A|As],[B|Bs],PrevA,PrevB,LEq,GEq,Diff,CnfH-CnfT):-!,
    CnfH=[[A,-B,Diff],
          [-A,B,Diff],
          [-PrevA,B,GEq],
          [-PrevB,A,LEq]
          |CnfM],
    unaryDiffCnf_aux(As,Bs,A,B,LEq,GEq,Diff,CnfM-CnfT).
unaryDiffCnf_aux([],[],PrevA,PrevB,LEq,GEq,_Diff,CnfH-CnfT):-!,
    CnfH=[[-PrevA,GEq],
          [-PrevB,LEq]
          |CnfT].
unaryDiffCnf_aux([A],[],PrevA,PrevB,LEq,GEq,Diff,CnfH-CnfT):-!,
    CnfH=[[-A,Diff],
          [-PrevA,GEq],
          [-PrevB,A,LEq]
          |CnfT].
unaryDiffCnf_aux([],[B],PrevA,PrevB,LEq,GEq,Diff,CnfH-CnfT):-!,
    CnfH=[[-B,Diff],
          [-PrevA,B,GEq],
          [-PrevB,LEq]
          |CnfT].



% --------------------------------
% | zIsUnaryDiffOne              |
% --------------------------------
% this component assumes the Unary number is [A,B|_]
unaryDiff1ReifSimplify(Constr,NewConstr,Changed):-!,
    Constr=bc(_Type,[Z,A,B]),
    (ground(Z) ->
         Changed=1, NewConstr=none,
         (Z =:=1 -> litUnify(A,B) ; litAsgnTrue(A), litAsgnFalse(B)) ;
    (ground(A) ->
         Changed=1, NewConstr=none,
         (A =:= 1 -> litUnify(B,Z) ; litAsgnTrue(Z)) ;
    (ground(B) ->
         Changed=1, NewConstr=none,
         (B =:= -1 -> litUnify(A, -Z) ; litAsgnTrue(Z)) ;
    (litIsEqual(A,B) ->
         Changed=1, NewConstr=none,
         litAsgnTrue(Z) ;
    NewConstr=Constr
    )))).

unaryDiff1Reif2cnf(bc(_,[Z,A,B]),CnfH-CnfT):-!,
    % (A and -B) <-> -Z
    CnfH=[
          [A,Z],
          [-B,Z],
          [-A,B,-Z]
          |CnfT].