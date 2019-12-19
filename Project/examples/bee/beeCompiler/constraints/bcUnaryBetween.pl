% Author: Amit Metodi
% Last Updated: 17/04/2017

:- module(bcUnaryBetween, [ ]).

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=int_between(A,B,C,ConstrsH-ConstrsT),
   Body=(
        bParser:int_geq(A,B,ConstrsH-ConstrsM),
        bParser:int_leq(A,C,ConstrsM-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).


:- if(bSettings:intNotBetween(decompose)).

:- Head=int_not_between(A,B,C,ConstrsH-ConstrsT),
   Body=(
        bParser:int_lt_reif(A,B,Rab,ConstrsH-ConstrsM1),
        bParser:int_gt_reif(A,C,Rac,ConstrsM1-ConstrsM2),
        bParser:bool_array_or([Rab,Rac],ConstrsM2-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- elif(bSettings:intNotBetween(decomposeXor)).

:- Head=int_not_between(A,B,C,ConstrsH-ConstrsT),
   Body=(
        bParser:int_lt_reif(A,B,Rab,ConstrsH-ConstrsM1),
        bParser:int_gt_reif(A,C,Rac,ConstrsM1-ConstrsM2),
        bParser:bool_array_xor([Rab,Rac],ConstrsM2-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

:- else.

:- Head=int_not_between(A,B,C,ConstrsH-ConstrsT),
   Body=(
         !,
         bcInteger:getUnaryNumber(A,Au),
         bcInteger:getUnaryNumber(B,Bu),
         bcInteger:getUnaryNumber(C,Cu),
         bcUnaryBetween:notBetweenType(Type),
         bcUnaryBetween:notBetweenSimplify(bc(Type,[Au, Bu, Cu]), Constr, 1),
         (Constr==none ->
             ConstrsH=ConstrsT
         ;
             ConstrsH=[Constr|ConstrsT]
         )
   ),
   bParser:addConstraint(Head,Body).


notBetweenType([
         bcUnaryBetween:notBetweenSimplify,
         skipSimplify,
         0,
         bcUnaryBetween:notBetween2cnf,
         notBetween
        ]):-!.

%% not(B <= A <= C)
notBetweenSimplify(Constr, NewConstr, Changed):-!,
    Constr=bc(Type,[A,B,C]),
    auxUnarynum:unarynumIsRangeChanged(A,NA,Changed),
    auxUnarynum:unarynumIsRangeChanged(B,NB,Changed),
    auxUnarynum:unarynumIsRangeChanged(C,NC,Changed),!,
    (Changed == 1 ->
        NA=(Amin,Amax,_),
        NB=(Bmin,Bmax,_),
        NC=(Cmin,Cmax,_),
        ((Amin > Cmax ; Amax < Bmin ; Bmin > Cmax) ->
            NewConstr = none ;
        (Amin==Amax -> % (C < A || A < B)   :   ((!(C >= A)) || (B >= A+1))
            auxUnarynum:unarynumGEqK(NC,Amin,CgeqA), %% C >= A
            Amin1 is Amin + 1,
            auxUnarynum:unarynumGEqK(NB,Amin1,BgeqA1), %% B >= A+1
            bcAtLeastOne:aloType(OrType),
            auxLiterals:lits2plits([BgeqA1, -CgeqA],Vec),
            bcAtLeastOne:aloSimplify(bc(OrType,Vec),NewConstr,_) ;
        (Amin >= Bmax ->  % B<=A -> A > C
            auxUnarynum:unarynumAddConst(NC,1,NNC),
            bcUnaryLEq:unaryLEqType(LEqType),
            bcUnaryLEq:unaryLEqSimplify(bc(LEqType,[NNC,NA]), NewConstr, 1) ;
        (Amax =< Cmin ->  % A<=C -> A < B
            auxUnarynum:unarynumAddConst(NA,1,NNA),
            bcUnaryLEq:unaryLEqType(LEqType),
            bcUnaryLEq:unaryLEqSimplify(bc(LEqType,[NNA,NB]), NewConstr, 1) ;
        ((Bmin==Bmax, Cmin==Cmax) ->
            !,Bmax =< Cmin,!,
            NewConstr=none,
            fixAnotBetween(NA,Bmax,Cmin, _) ;
        (Bmax =< Cmin ->
            Diff is Bmax - Cmin - 1,
            auxUnarynum:unarynumAddConst(NC,Diff,FC),
            fixAnotBetween(NA,Bmax,Cmin,FA),
            notBetweenFocusVars(FA,NB,FC,XA,XB,XC),
            NewConstr = bc(Type,[XA,XB,XC]) ;
        notBetweenFocusVars(NA,NB,NC,FA,FB,FC),
        NewConstr = bc(Type,[FA,FB,FC])
        ))))))
    ;
        NewConstr = Constr
    ).
        
fixAnotBetween(A,Imin,Imax,FA):-!,
    A=(Amin,Amax,Bits,Lbit),
    Keep is Imin - Amin,
    Unify is Imax - Imin + 1,
    fixAnotBetween_keep(Keep,Bits,Unify,FBits),
    FAmax is Amax - Unify,
    FA=(Amin,FAmax,FBits,Lbit).

fixAnotBetween_keep(Keep,[Bi|Bits],Unify,[Bi|FBits]):-!,
    (Keep > 1 ->
        Keep1 is Keep - 1,
        fixAnotBetween_keep(Keep1,Bits,Unify,FBits)
    ;
        auxLiterals:lit2plit(Bi,B0l,B0op),
        fixAnotBetween_unify(Unify,(B0l,B0op),Bits,FBits)
    ).

fixAnotBetween_unify(0,_,Bits,Bits):-!.
fixAnotBetween_unify(Unify,B0,[Bi|Bits],FBits):-!,
    auxLiterals:lit2plit(Bi,Bil,Biop),
    auxLiterals:plitUnify(B0,(Bil,Biop)),
    Unify1 is Unify - 1,
    fixAnotBetween_unify(Unify1,B0,Bits,FBits).


notBetweenFocusVars(A,B,C,NA,NB,NC):-
    A=(Amin,Amax,_),
    B=(Bmin,Bmax,_),
    C=(Cmin,Cmax,_),
    FBmin is max(Bmin,Amin),
    FCmin is max(Cmin,FBmin - 1),
    FAmin is max(Amin,FBmin - 1),
    FCmax is min(Cmax,Amax),
    FBmax is min(Bmax,FCmax + 1),
    FAmax is min(Amax,FCmax + 1),
    auxUnarynum:unarynumFocusOn(A,FAmin,FAmax,NA),
    auxUnarynum:unarynumFocusOn(B,FBmin,FBmax,NB),
    auxUnarynum:unarynumFocusOn(C,FCmin,FCmax,NC).


notBetween2cnf(bc(_Type,[A,B,C]),CnfH-CnfT):-!,
    fixAnC(A,C,FA,FC),!,
    FA=(Amin,_Amax,Abits,_),
    B=(Bmin,_Bmax,Bbits,_),
    FC=(_Cmin,_Cmax,Cbits,_),
    (Amin==Bmin ->
        encodeNotBetween([1|Abits],Bbits,[1|Cbits],CnfH-CnfT)
    ;
        Add is Bmin - Amin - 1,
        auxLists:listSplit(Add, FBbits, Trues, Bbits),
        auxLiterals:litAsgnTrues(Trues),
        encodeNotBetween(Abits,FBbits,Cbits,CnfH-CnfT)
    ).


fixAnC(A,C,FA,FC):-!,
    A=(Amin,Amax,Abits,LAbit),
    C=(Cmin,Cmax,Cbits,LCbit),
    (Amin==Cmin -> FA=A, FC=C ;
    (Amin<Cmin ->
        FA=A,
        Add is Cmin - Amin,
        auxLists:listSplit(Add, FCbits, Trues, Cbits),
        auxLiterals:litAsgnTrues(Trues),
        FC = (Amin,Cmax, FCbits, LCbit)
    ;
        FC=C,
        Add is Amin - Cmin,
        auxLists:listSplit(Add, FAbits, Trues, Abits),
        auxLiterals:litAsgnTrues(Trues),
        FA = (Cmin,Amax, FAbits, LAbit)
    )).
    
encodeNotBetween([A0,A1|Abits],Bbits,Cbits,CnfH-CnfT):-!,
    (Bbits=[B1|BbitsR] ; (B1 = -1 , BbitsR=[])),!,
    (Cbits=[C0|CbitsR] ; (C0 = -1 , CbitsR=[])),!,
    CnfH=[[-A0, A1, B1, -C0]|CnfM],
    encodeNotBetween_step1(Abits,A1,BbitsR,CbitsR,CnfM-CnfT).
encodeNotBetween([A0],Bbits,Cbits,CnfH-CnfT):-!,
    (Bbits=[B1|_] ; B1 = -1),!,
    (Cbits=[C0|_] ; C0 = -1),!,
    CnfH=[[-A0, B1, -C0]|CnfT].

encodeNotBetween_step1([A2|Abits],A1,[B2|FBbits],[C1|Cbits],CnfH-CnfT):-!,
    CnfH=[[-A1, A2, B2, -C1]|CnfM],
    encodeNotBetween_step1(Abits,A2,FBbits,Cbits,CnfM-CnfT).
encodeNotBetween_step1([],_,[],[],Cnf-Cnf):-!.
encodeNotBetween_step1([_],_,[],[],Cnf-Cnf):-!.
encodeNotBetween_step1([],A1,FBbits,Cbits,CnfH-CnfT):-!,
    encodeNotBetween_step1([-1],A1,FBbits,Cbits,CnfH-CnfT).
encodeNotBetween_step1(Abits,A1,[],Cbits,CnfH-CnfT):-!,
    encodeNotBetween_step1(Abits,A1,[-1],Cbits,CnfH-CnfT).
encodeNotBetween_step1(Abits,A1,FBbits,[],CnfH-CnfT):-!,
    encodeNotBetween_step1(Abits,A1,FBbits,[-1],CnfH-CnfT).
:- endif.