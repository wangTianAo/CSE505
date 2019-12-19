% Author: Amit Metodi
% Last Updated: 19/05/2017

:- module(bcUnaryTimes, [ ]).
:- use_module('../auxs/auxLiterals').

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%

:- Head=int_times(A,B,C,ConstrsH-ConstrsT),
   Body=(
       !,
       bcInteger:getUnaryNumber(A,Au),
       bcInteger:getUnaryNumber(B,Bu),
       bcInteger:getUnaryNumber(C,Cu),
       bcUnaryTimes:utimesType(Type),
       bcUnaryTimes:utimesSimplify(bc(Type,[Au, Bu, Cu]), Constr, 1),
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
utimesType([
            bcUnaryTimes:utimesSimplify,
            skipSimplify,
            bcUnaryTimes:utimesDecompose,
            0,
            utimes
           ]).
upostimesType([
            bcUnaryTimes:upostimesSimplify,
            skipSimplify,
            0,
            bcUnaryTimes:upostimes2cnf,
            utimespos
           ]).


% ---------------------------------
% | Simplify Unary Times          |
% ---------------------------------
utimesSimplify(Constr, NewConstr, Changed):-!,
    Constr=bc(Type,[A,B,C]),
    auxUnarynum:unarynumIsChangedOrConst(A,NA,Changed),
    auxUnarynum:unarynumIsChangedOrConst(B,NB,Changed),
    auxUnarynum:unarynumIsRangeChanged(C,NC,Changed),!,
    (Changed==1 ->
        (NA=(Aval,Aval,_) ->
            NewConstr=none,
            auxUnarynum:unarynumMulByConst(NB,Aval,FB),
            auxUnarynum:unarynumEquals(FB,NC) ;
        (NB=(Bval,Bval,_) ->
            NewConstr=none,
            auxUnarynum:unarynumMulByConst(NA,Bval,FA),
            auxUnarynum:unarynumEquals(FA,NC) ;
        utimesBoundPropg(NA,NB,NC,FA,FB,FC,Changed2,AllPos),
        (AllPos==1 ->
            upostimesType(PosType),
            upostimesSimplify(bc(PosType,[FA,FB,FC]), NewConstr, 1) ;
        (Changed2==1 ->
            utimesSimplify(bc(Type,[FA,FB,FC]), NewConstr, 1)
        ;
            NewConstr=bc(Type,[FA,FB,FC])
        ))))
    ;
        NewConstr=Constr
    ).

utimesBoundPropg(A,B,C,NA,NB,NC,Changed,AllPos):-!,
    A=(Amin,Amax,_),
    B=(Bmin,Bmax,_),
    ((Amin >= 0 , Bmin >= 0) -> % (A=pos,B=pos)
        Changed=1,
        AllPos=1,
        auxUnarynum:unarynumSetMin(C,0,FC),
        upostimesBoundPropg(A,B,FC,NA,NB,NC,_) ;
    ((Amax =<0 , Bmax =<0) -> % (A=neg,B=neg)
        Changed=1,
        AllPos=1,
        auxUnarynum:unarynumNeg(A,NgA),
        auxUnarynum:unarynumNeg(B,NgB),
        auxUnarynum:unarynumSetMin(C,0,FC),
        upostimesBoundPropg(NgA,NgB,FC,NA,NB,NC,_) ;
    ((Amax =< 0, Amin < 0) -> % (A=neg)
        Changed=1,
        auxUnarynum:unarynumNeg(A,NgA),
        auxUnarynum:unarynumNeg(C,NgC),
        utimesBoundPropg(NgA,B,NgC,NA,NB,NC,_,AllPos) ;
    ((Bmax =< 0, Bmin < 0) -> % (B=neg)
        Changed=1,
        auxUnarynum:unarynumNeg(B,NgB),
        auxUnarynum:unarynumNeg(C,NgC),
        utimesBoundPropg(NgB,A,NgC,NA,NB,NC,_,AllPos) ;
    (Bmin >= 0 -> % (B=pos) and -inf < A < inf
        Changed=1,
        utimesBoundPropg(B,A,C,NA,NB,NC,_,AllPos) ;

    C=(Cmin,Cmax,_),
    ((Cmin >=0, Amin >= 0) -> % (A=pos, C=pos)
        Changed=1,
        AllPos=1,
        auxUnarynum:unarynumSetMin(B,0,FB),
        upostimesBoundPropg(A,FB,C,NA,NB,NC,_) ;
    ((Cmax =<0, Amin >= 0) -> % (A=pos, C=neg)
        Changed=1,
        AllPos=1,
        auxUnarynum:unarynumNeg(B,NgB),
        auxUnarynum:unarynumSetMin(NgB,0,FB),
        auxUnarynum:unarynumNeg(C,NgC),
        upostimesBoundPropg(A,FB,NgC,NA,NB,NC,_) ;

    ((Cmax =<0, Cmin < 0) ->  %% (C=neg) and (-inf<A<inf) and (-inf<B<inf)
        % (Cmin < 0) is for avoid endless loop when Cmax==Cmin==0
        Changed=1,
        auxUnarynum:unarynumNeg(B,NgB),
        auxUnarynum:unarynumNeg(C,NgC),
        utimesBoundPropg(A,NgB,NgC,NA,NB,NC,_,AllPos) ;

    %%% left with the possible ranges
    % (both,both,both)
    % (pos,both,both)
    % (both,both,pos)
    NA=A,
    (Amin > 0 ->
        NBmin is max(Bmin, Cmin // Amin),
        NBmax is min(Bmax, Cmax // Amin),
        auxUnarynum:unarynumBoundsChanged(B,NBmin,NBmax,NB,Changed)
    ;
        NBmin=Bmin, NBmax=Bmax,
        NB=B
    ),
    NCmin is max(Cmin,min(Amin*NBmin,min(Amin*NBmax,Amax*NBmin))),
    NCmax is min(Cmax,max(Amin*NBmin,Amax*NBmax)),
%    Cmin2 is max(Cmin,min(min(Amin*Bmin,Amin*Bmax),min(Amax*Bmin,Amax*Bmax))),
%    Cmax2 is min(Cmax,max(max(Amin*Bmin,Amin*Bmax),max(Amax*Bmin,Amax*Bmax))),
    auxUnarynum:unarynumBoundsChanged(C,NCmin,NCmax,NC,Changed)
    )))))))).




% ---------------------------------
% | Simplify Positive Unary Times |
% ---------------------------------
upostimesSimplify(Constr, NewConstr, Changed):-!,
     Constr=bc(Type,[A,B,C]),
     auxUnarynum:unarynumIsChangedOrConst(A,NA,Changed),
     auxUnarynum:unarynumIsChangedOrConst(B,NB,Changed),
     auxUnarynum:unarynumIsChangedOrConst(C,NC,Changed),!,
     (Changed==1 ->
        (NA=(Aval,Aval,_) ->
            NewConstr=none,
            auxUnarynum:unarynumMulByConst(NB,Aval,FB),
            auxUnarynum:unarynumEquals(FB,NC) ;
        (NB=(Bval,Bval,_) ->
            NewConstr=none,
            auxUnarynum:unarynumMulByConst(NA,Bval,FA),
            auxUnarynum:unarynumEquals(FA,NC) ;
        (NC=(Cval,Cval,_) ->
            (Cval > 0 ->
                NewConstr=none,
                unaryPosTimesEqK(NA,NB,Cval)
            ;
                unaryPosTimesEq0(NA,NB,NewConstr)
            ) ;
         upostimesBoundPropg(NA,NB,NC,NNA,NNB,NNC,DomChanged),
         (DomChanged==1 ->
               upostimesSimplify(bc(Type,[NNA,NNB,NNC]), NewConstr, 1)
         ;
               NewConstr=bc(Type,[NNA,NNB,NNC])
         ))))
     ;
         NewConstr=Constr
     ).


% --------------------------------
% |   Unary Times Simplify -     |
% |   Boundary propagation       |
% --------------------------------
upostimesBoundPropg(A,B,C,NA,NB,NC,Changed):-!,
    A=(Amin,Amax,_),
    B=(Bmin,Bmax,_),
    C=(Cmin,Cmax,_),
    
    % New A,B minimum
    NAmin is max(Amin, ceil(Cmin / Bmax)),
    NBmin is max(Bmin, ceil(Cmin / Amax)),
    % New A,B maximum
    (NBmin > 0 ->
        NAmax is min(Amax, Cmax // NBmin)
    ;
        NAmax is Amax
    ),
    (NAmin > 0 ->
        NBmax is min(Bmax, Cmax // NAmin)
    ;
        NBmax is Bmax
    ),
    % New C minimum and maximum
    (NAmin*NBmin >= Cmin ->
        NCmin is max(Cmin, NAmin * NBmin)
    ;
        NCmin is max(Cmin, min((NAmin+1)*NBmin,NAmin*(NBmin+1)))
    ),
    (NAmax*NBmax =< Cmax ->
        NCmax is min(Cmax, NAmax * NBmax)
    ;
        NCmax is min(Cmax, max((NAmax-1)*NBmax,NAmax*(NBmax-1)))
    ),

    auxUnarynum:unarynumBoundsChanged(A,NAmin,NAmax,NA,Changed),
    auxUnarynum:unarynumBoundsChanged(B,NBmin,NBmax,NB,Changed),
    auxUnarynum:unarynumBoundsChanged(C,NCmin,NCmax,NC,Changed).


% -------------------------
% | Positive Unary Times  |
% |    Special Cases      |
% -------------------------

unaryPosTimesEqK((Amin,Amax,Abits,_),(Bmin,Bmax,Bbits,_),K):-
    reverse(Bbits,BbitsR),!,
    unaryPosTimesEqK_A(Abits,Amin,1,Bmax,BbitsR,K),!,
    reverse(Abits,AbitsR),!,
    unaryPosTimesEqK_A(Bbits,Bmin,1,Amax,AbitsR,K).

unaryPosTimesEqK_A([Ai|As],I,Aim1, Bmax,Bs, K):-
    I1 is I + 1,
    (K mod I =:= 0 ->
        J is K // I,
        unaryPosTimesEqK_getB(Bmax,J,Bs,Bj,RBs),
        litUnify(-Ai,Bj),
        unaryPosTimesEqK_A(As,I1,Ai, J,RBs, K)
    ;
        litUnify(Ai,Aim1),
        unaryPosTimesEqK_A(As,I1,Ai, Bmax,Bs, K)
    ).
unaryPosTimesEqK_A([],_,_, _,_, _):-!.


unaryPosTimesEqK_getB(Bval,Bval,[],1,[]):-!.
unaryPosTimesEqK_getB(Bval,Bval,[B|Bs],B,[B|Bs]):-!.
unaryPosTimesEqK_getB(Bmax,Bval,Bs,Bj,RBs):-
    Bval < Bmax,!,
    Drop is Bmax - Bval,
    auxLists:listDropFrom(Drop,Bs,RBs),
    (RBs=[Bj|_] ; (RBs=[], Bj=1)).


unaryPosTimesEq0((Amin,_,[A0|_],_),(Bmin,_,[B0|_],_),Constr):-
    ((Amin > 0 , Bmin==0) ->
        Constr=none,
        litAsgnFalse(B0) ;
    ((Bmin > 0 , Amin==0) ->
        Constr=none,
        litAsgnFalse(A0) ;
    ((Amin==0, Bmin==0) ->
       bcAtLeastOne:aloType(Type),
       auxLiterals:lits2plits([-A0,-B0],Vec),
       bcAtLeastOne:aloSimplify(bc(Type,Vec),Constr,_)
    ;
        throw(unsat)
    ))).


% --------------------------------
% |     decompose unary times    |
% --------------------------------
utimesDecompose(bc(_,[A,B,C]),Constrs):-!,
    (C=(0,0,_) -> % (A=both , B=both)
        auxUnarynum:unarynumFocusOn(A,-1,1,(-1,1,[A0,A1],_)),
        auxUnarynum:unarynumFocusOn(B,-1,1,(-1,1,[B0,B1],_)),
        bcAtLeastOne:aloType(ALOType),
        auxLiterals:lits2plits([Aeq0,Beq0],OrVec),
        bcUnaryDiffReif:unaryDiffKReifType(DiffType),
        Constrs=[
                 bc(DiffType,[-Aeq0,A0,A1]),
                 bc(DiffType,[-Beq0,B0,B1]),
                 bc(ALOType,OrVec)
                ]
    ;

    % (both,both,both)
    % (pos,both,both)
    % (both,both,pos)

    % Get B pos and neg
    bcUnaryAbs:splitUnaryNumToPosNeg(B,Bpos,Bneg),
    Bpos=(_,Bmax1,[Bgt0|_],_),
    Bneg=(_,Bmax2,[Blt0|_],_),
    Bmax3 is max(Bmax1,Bmax2),
    auxUnarynum:unarynumNewInRange(0,Bmax3,BMAXu),!,

    % Get A pos and neg
    A=(Amin,_),
    (Amin >=0 -> % (pos,both,both)
        Alt0= -1,
        (Amin>0 ->
            Agt0=1
        ;
            A=(_,_,[Agt0|_],_)
        ),
        AMAXu=A,
        MaxAconstr=none
    ;
        bcUnaryAbs:splitUnaryNumToPosNeg(A,Apos,Aneg),
        Apos=(_,Amax1,[Agt0|_],_),
        Aneg=(_,Amax2,[Alt0|_],_),
        Amax3 is max(Amax1,Amax2),
        auxUnarynum:unarynumNewInRange(0,Amax3,AMAXu),
        MaxAconstr=bc(MaxType,[AMAXu,Apos,Aneg])
    ),!,
    
    % Get C pos and neg
    C=(Cmin,_),
    (Cmin >= 0 ->
        Clt0= -1,
        (Cmin>0 ->
            Cgt0=1
        ;
            C=(_,_,[Cgt0|_],_)
        ),
        CMAXu=C,
        MaxCconstr=none
    ;
        bcUnaryAbs:splitUnaryNumToPosNeg(C,Cpos,Cneg),
        Cpos=(_,Cmax1,[Cgt0|_],_),
        Cneg=(_,Cmax2,[Clt0|_],_),
        Cmax3 is max(Cmax1,Cmax2),
        auxUnarynum:unarynumNewInRange(0,Cmax3,CMAXu),
        MaxCconstr=bc(MaxType,[CMAXu,Cpos,Cneg])
    ),!,
    
    bcAtLeastOne:aloType(ALOType),
    auxLiterals:lits2plits([-Agt0,-Bgt0,Cgt0],OrVec1),
    auxLiterals:lits2plits([-Alt0,-Blt0,Cgt0],OrVec2),
    auxLiterals:lits2plits([-Agt0,-Blt0,Clt0],OrVec3),
    auxLiterals:lits2plits([-Alt0,-Bgt0,Clt0],OrVec4),

    bcUnaryMax:unaryMaxType(MaxType),

    upostimesType(TimesType),!,
    upostimesSimplify(bc(TimesType,[AMAXu,BMAXu,CMAXu]), TimeConstr, 1),!,

    RConstrs=[
              MaxAconstr,
              bc(MaxType,[BMAXu,Bpos,Bneg]),
              MaxCconstr,
              TimeConstr,
              bc(ALOType,OrVec1),
              bc(ALOType,OrVec2),
              bc(ALOType,OrVec3),
              bc(ALOType,OrVec4)
             ],
    removeNoneConstrs(RConstrs,Constrs)
    ).

removeNoneConstrs([none|Cs],NNCs):-!,
    removeNoneConstrs(Cs,NNCs).
removeNoneConstrs([C|Cs],[C|NNCs]):-!,
    removeNoneConstrs(Cs,NNCs).
removeNoneConstrs([],[]):-!.


% --------------------------
% | encode pos unary times |
% --------------------------
upostimes2cnf(bc(_,[A,B,C]),CnfH-CnfT):-!,
    A=(Amin,Amax,Abits,_),
    B=(Bmin,Bmax,Bbits,_),
    C=(Cmin,_,Cbits,_),
    I1 is Amin + 1,
    J1 is Bmin + 1,
    K1 is Cmin + 1,
    % positive
    aiNbDargC(Abits,I1,Bbits,J1,Cbits,K1,CnfH-CnfM1),

    (Bmin > 0 ->
        aiDragC(Abits,I1,Bmin,Cbits,K1,CnfM1-CnfM2)
    ;
        CnfM1=CnfM2
    ),
    (Amin > 0 ->
        aiDragC(Bbits,J1,Amin,Cbits,K1,CnfM2-CnfM3)
    ;
        CnfM2=CnfM3
    ),
    (Cmin==0 -> %  -> at least one of Amin or Bmin equals 0
        Cbits=[Cmbit|_],
        ((Amin==0, Bmin==0) ->
            Abits=[Ambit|_],
            Bbits=[Bmbit|_],
            CnfM3=[[Ambit,-Cmbit],[Bmbit,-Cmbit]|CnfM4]
        ;
        (Amin==0 ->
            Abits=[Ambit|_],
            CnfM3=[[Ambit,-Cmbit]|CnfM4]
        ;
            Bbits=[Bmbit|_],
            CnfM3=[[Bmbit,-Cmbit]|CnfM4]

        ))
    ;
        CnfM3=CnfM4
    ),
    % negative
    ((Amax>1 ; Bmax>1) ->
        (Amax>1 ->
            auxUnarynum:unarynumFocusOn(A,1,Amax,(Amin2,_,Abits2,_))
        ;
            Amin2=1, Abits2=[-1]
        ),!,
        (Bmax>1 ->
            auxUnarynum:unarynumFocusOn(B,1,Bmax,(Bmin2,_,Bbits2,_))
        ;
            Bmin2=1, Bbits2=[-1]
        ),!,
        I2 is Amin2 + 1,
        J2 is Bmin2 + 1,!,
        naiNnbDargnC(Abits2,I2,Bbits2,J2,Cbits,K1,CnfM4-CnfT)
    ;
        CnfM4=CnfT
    ).

aiNbDargC([Ai|As],I,Bs,Bmin,Cs,Cmin,CnfH-CnfT):-!,
    aiNbjDragCij(Bs,Bmin,Ai,I,Cs,Cmin,CnfH-CnfM),!,
    I1 is I + 1,
    aiNbDargC(As,I1,Bs,Bmin,Cs,Cmin,CnfM-CnfT).
aiNbDargC([],_,_,_,_,_,Cnf-Cnf):-!.

aiNbjDragCij([Bj|Bs],J,Ai,I,Cs,Cmin,CnfH-CnfT):-!,
    CDrop is I * J - Cmin,
    (CDrop >= 0 ->
        (auxLists:listDropFrom(CDrop,Cs,[Cij|RCs]) ->
            CnfH =[[-Ai, -Bj, Cij]|CnfM],
            NCmin is I * J + 1,
            J1 is J + 1,
            aiNbjDragCij(Bs,J1,Ai,I,RCs,NCmin,CnfM-CnfT)
        ;
            CnfH =[[-Ai, -Bj]|CnfM],
            aiNbjDragFlase(Bs,Ai,CnfM-CnfT)
        )
    ;
        J1 is J + 1,
        aiNbjDragCij(Bs,J1,Ai,I,Cs,Cmin,CnfH-CnfT)
    ).
aiNbjDragCij([],_,_,_,_,_,Cnf-Cnf):-!.


aiNbjDragFlase([Bj|Bs],Ai,[[-Ai,-Bj]|CnfH]-CnfT):-!,
    aiNbjDragFlase(Bs,Ai,CnfH-CnfT).
aiNbjDragFlase([],_,Cnf-Cnf):-!.



aiDragC([Ai|As],I,Bmin,Cs,Cmin,CnfH-CnfT):-
    CDrop is I * Bmin - Cmin,
    (CDrop >= 0 ->
        (auxLists:listDropFrom(CDrop,Cs,[Cimin|RCs]) ->
            CnfH =[[-Ai, Cimin]|CnfM],
            NCmin is I * Bmin + 1,
            I1 is I + 1,
            aiDragC(As,I1,Bmin,RCs,NCmin,CnfM-CnfT)
        ;
            CnfH =[[-Ai]|CnfT]
        )
    ;
        I1 is I + 1,
        aiDragC(As,I1,Bmin,Cs,Cmin,CnfH-CnfT)
    ).
aiDragC([],_,_,_,_,Cnf-Cnf):-!.






naiNnbDargnC([Ai|As],I,Bs,Bmin,Cs,Cmin,CnfH-CnfT):-!,
    naiNnbjDragnCij(Bs,Bmin,Ai,I,Cs,Cmin,CnfH-CnfM),!,
    I1 is I + 1,
    naiNnbDargnC(As,I1,Bs,Bmin,Cs,Cmin,CnfM-CnfT).
naiNnbDargnC([],I,Bs,Bmin,Cs,Cmin,CnfH-CnfT):-!,
    nbjDragnCij(Bs,Bmin,I,Cs,Cmin,CnfH-CnfT).

%naiNnbDargnC([],_,_,_,_,_,Cnf-Cnf):-!.

naiNnbjDragnCij([Bj|Bs],J,Ai,I,Cs,Cmin,CnfH-CnfT):-!,
    CDrop is (I - 1) * (J - 1) + 1 - Cmin,
    (CDrop >= 0 ->
        (auxLists:listDropFrom(CDrop,Cs,[Cij|RCs]) ->
            CnfH =[[Ai, Bj, -Cij]|CnfM],
            NCmin is (I - 1) * (J - 1) + 2,
            J1 is J + 1,
            naiNnbjDragnCij(Bs,J1,Ai,I,RCs,NCmin,CnfM-CnfT)
        ;
            CnfH=CnfT
        )
    ;
        J1 is J + 1,
        CnfH =[[Ai, Bj]|CnfM],
        naiNnbjDragnCij(Bs,J1,Ai,I,Cs,Cmin,CnfM-CnfT)
    ).
naiNnbjDragnCij([],J,Ai,I,Cs,Cmin,CnfH-CnfT):-!,
    CDrop is (I - 1) * (J - 1) + 1 - Cmin,
    (CDrop >= 0 ->
        (auxLists:listDropFrom(CDrop,Cs,[Cij|_]) ->
            CnfH =[[Ai, -Cij]|CnfT]
        ;
            CnfH=CnfT
        )
    ;
        CnfH =[[Ai]|CnfT]
    ).
naiNnbjDragnFalse([Bj|Bs],Ai,[[Ai,Bj]|CnfH]-CnfT):-!,
    naiNnbjDragnFalse(Bs,Ai,CnfH-CnfT).
naiNnbjDragnFalse([],_,Cnf-Cnf):-!.


nbjDragnCij([Bj|Bs],J,I,Cs,Cmin,CnfH-CnfT):-!,
    CDrop is (I - 1) * (J - 1) + 1 - Cmin,
    (CDrop >= 0 ->
        (auxLists:listDropFrom(CDrop,Cs,[Cij|RCs]) ->
            CnfH =[[Bj, -Cij]|CnfM],
            NCmin is (I - 1) * (J - 1) + 2,
            J1 is J + 1,
            nbjDragnCij(Bs,J1,I,RCs,NCmin,CnfM-CnfT)
        ;
            CnfH=CnfT
        )
    ;
        J1 is J + 1,
        CnfH =[[Bj]|CnfM],
        nbjDragnCij(Bs,J1,I,Cs,Cmin,CnfM-CnfT)
    ).
nbjDragnCij([],J,I,Cs,Cmin,CnfH-CnfT):-!,
    CDrop is (I - 1) * (J - 1) + 1 - Cmin,
    CDrop >= 0, % assert
    (auxLists:listDropFrom(CDrop,Cs,[Cij|_]) ->
        CnfH =[[-Cij]|CnfT]
    ;
        CnfH=CnfT
    ).