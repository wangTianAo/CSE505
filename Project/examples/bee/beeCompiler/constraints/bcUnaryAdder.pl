% Author: Amit Metodi
% Last Updated: 11/06/2013

:- module(bcUnaryAdder, [ ]).
:- use_module('../auxs/auxLiterals').


%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%

:- Head=int_plus(A,B,C,ConstrsH-ConstrsT),
   Body=(
       !,
       bcInteger:getUnaryNumber(A,Au),
       bcInteger:getUnaryNumber(B,Bu),
       bcInteger:getUnaryNumber(C,Cu),
       bcUnaryAdder:uadderSimplify1st(bc(_,[Au, Bu, Cu]), Constr, _),
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
uadderType([
            bcUnaryAdder:uadderSimplify1st,
            skipSimplify,
            0,
            0,
            uadder
           ]).
:- if(bSettings:unaryAdderType(uadder)).
uadder2ndType([
            bcUnaryAdder:uadderSimplify,
            skipSimplify,
            0,
            bcUnaryAdder:uadder2cnf,
            uadder
           ]).
:- elif(bSettings:unaryAdderType(merger)).
uadder2ndType([
            bcUnaryAdder:uadderSimplify,
            skipSimplify,
            bcUnaryAdder:mergerDecompose,
            0,
            uadder
           ]).
:- elif(bSettings:unaryAdderType(hybrid)).
uadder2ndType([
            bcUnaryAdder:uadderSimplify,
            skipSimplify,
            bcUnaryAdder:hybridDecompose,
            0,
            uadder
           ]).
:- else.
:- bSettings:unaryAdderType(X), writef('ERROR: "%w" is wrong value for bSettings:unaryAdderType !\n',[X]),flush_output,halt.
:- endif.

% --------------------------------
% | Reduce Unary Adder           |
% --------------------------------
uadderSimplify1st(bc(_,[A, B, C]), Constr, Changed):-!,
     auxUnarynum:unarynumIsChangedOrConst(A,NA,Changed),
     auxUnarynum:unarynumIsChangedOrConst(B,NB,Changed),
     auxUnarynum:unarynumIsChangedOrConst(C,NC,Changed),!,
     uadderBoundPropg(NA,NB,NC,NNA,NNB,NNC,DomChanged),
     Changed=DomChanged,
     (specialCases(NNA,NNB,NNC,Constr) ;
      (
       uadder2ndType(Type),
       Constr=bc(Type,[NNA,NNB,NNC])
     )).

uadderSimplify(Constr, NewConstr, Changed):-!,
     Constr=bc(Type,[A, B, C]),
     auxUnarynum:unarynumIsChangedOrConst(A,NA,Changed),
     auxUnarynum:unarynumIsChangedOrConst(B,NB,Changed),
     auxUnarynum:unarynumIsChangedOrConst(C,NC,Changed),!,
     (Changed==1 ->
         uadderBoundPropg(NA,NB,NC,NNA,NNB,NNC,DomChanged),
         (specialCases(NNA,NNB,NNC,NewConstr) ;
         (DomChanged==1 ->
               uadderSimplify(bc(Type,[NNA,NNB,NNC]), NewConstr, _)
         ;
               NewConstr=bc(Type,[NNA,NNB,NNC])
         ))
     ;
         NewConstr=Constr
     ).

% --------------------------------
% |   Unary Adder Simplify -     |
% |       Special Cases          |
% --------------------------------
specialCases(A,B,C,Constr):-!,
   A=(0,Amax,Abits,_),
   B=(0,Bmax,Bbits,_),
   C=(Cmin,Cmax,Cbits,_),
   (Amax==0 ->
        auxUnarynum:unarynumEquals(B,C),
        Constr=none ;
   (Bmax==0 ->
        auxUnarynum:unarynumEquals(A,C),
        Constr=none ;
   (Cmin==Cmax ->
        litNotReverseXs(Abits,RNAbits),
        litUnifies(RNAbits,Bbits),
        Constr=none ;
   ((Amax==1, Bmax==1) ->
        Abits=[X1],
        Bbits=[X2],
        (Cmin==0 ->
           (Cmax==2 ->
               Cbits=[Y1,Y2]
           ;
               Cbits=[Y1],
               Y2= -1
           )
        ;
           Y1= 1,
           Cbits=[Y2]
        ),!,
        bcComparator:comparatorType(CType),
        bcComparator:comparatorSimplify(bc(CType,[X1,X2,Y1,Y2]), Constr, _)
   ;
   ((Cmax - Cmin =:= 1 , (Amax==1 ; Bmax==1)) ->
        Cbits=[X2],
        (Amax==1 ->
           Abits=[X1],
           Bbits=[Y1,Y2]
        ;
           Bbits=[X1],
           Abits=[Y1,Y2]
        ),!,
        bcComparator:comparatorType(CType),
        bcComparator:comparatorSimplify(bc(CType,[X1,-X2,-Y2,-Y1]), Constr, _)
   ;
   !,fail
   ))))).

% --------------------------------
% |   Unary Adder Simplify -     |
% |   Boundary propagation       |
% --------------------------------
uadderBoundPropg(A,B,C,NA,NB,NC,Changed):-!,
     A=(Amin,Amax,_),
     B=(Bmin,Bmax,_),
     C=(Cmin,Cmax,_),

     Amin2 is max(Amin, Cmin - Bmax),
     Bmin2 is max(Bmin, Cmin - Amax),

     Amax2 is min(Amax, Cmax - Bmin2),
     Bmax2 is min(Bmax, Cmax - Amin2),

     Cmin2 is max(Cmin, Amin2 + Bmin2),
     Cmax2 is min(Cmax, Amax2 + Bmax2),

     auxUnarynum:unarynumBoundsChanged(A,Amin2,Amax2,(Amin2,Amax2,NAbits),Changed),
     auxUnarynum:unarynumBoundsChanged(B,Bmin2,Bmax2,(Bmin2,Bmax2,NBbits),Changed),
     auxUnarynum:unarynumBoundsChanged(C,Cmin2,Cmax2,(Cmin2,Cmax2,NCbits),Changed),

     Amax3 is Amax2 - Amin2,
     Bmax3 is Bmax2 - Bmin2,
     Cmin3 is Cmin2 - Amin2 - Bmin2,
     Cmax3 is Cmax2 - Amin2 - Bmin2,
     !,
     NA=(0,Amax3,NAbits),
     NB=(0,Bmax3,NBbits),
     NC=(Cmin3,Cmax3,NCbits).



% --------------------------------
% |     Unary Adder Rotation     |
% --------------------------------

uadderCnfSimplify(A,B,C,NA,NB,NY):-!,
    A=(0,Amax,Abits,_),
    B=(0,Bmax,Bbits,_),
    C=(Ymin,Ymax,Ybits,_),
    rotateAdder(Amax,Abits,Bmax,Bbits,Ymin,Ymax,Ybits,NA,NB,NY).

rotateAdder(Amax,Abits,Bmax,Bbits,Ymin,Ymax,Ybits,A,B,C):-
    Bmax > Amax,!,
    rotateAdder(Bmax,Bbits,Amax,Abits,Ymin,Ymax,Ybits,A,B,C).
rotateAdder(Amax,Abits,Bmax,Bbits,Ymin,Ymax,Ybits,A,B,C):-
    Ysize is Ymax - Ymin,
    (Ysize >= Amax ->
        A=(Amax,Abits),
        B=(Bmax,Bbits),
        C=(Ymin,Ymax,Ybits) ;
    % Abits + Bbits = Ybits + minY
    % => Abits = Cbits - Bbits + minY
    % => Abits = Cbits + (not_rev(Bbits) - Bmax) + minY
    % => Abits +(Bmax - minY) = Ybits + not_rev(Bbits)
    auxLiterals:litNotReverseXs(Bbits,RNBbits),
    NCmin is Bmax - Ymin,
    NCmax is Amax + NCmin,
    C=(NCmin,NCmax,Abits),
    (Ysize >= Bmax ->
        B=(Bmax,RNBbits),
        A=(Ysize,Ybits)
    ;
        A=(Bmax,RNBbits),
        B=(Ysize,Ybits)
    )).


:- if((bSettings:unaryAdderType(uadder) ; bSettings:unaryAdderType(hybrid))).

% ---------- UAdder Cnf ----------
uadder2cnf(bc(_,[A, B, C]), CnfH-CnfT):-!,
      uadderCnfSimplify(A,B,C,(Amax,Abits),(Bmax,Bbits),(Ymin,_Ymax,Ybits)),!,

      auxLists:listDropFrom(Ymin,Abits,Abits1),
      xiDragYi(Abits1, Ybits, CnfH-Cnf1),!,
      auxLists:listDropFrom(Ymin,Bbits,Bbits1),
      xiDragYi(Bbits1, Ybits, Cnf2-Cnf3),!,

      AdropY is Bmax - Ymin,
      auxLists:listDropFrom(AdropY,Ybits,Ybits4As),
      xiDragYi(Ybits4As, Abits, Cnf1-Cnf2),!,
      BdropY is Amax - Ymin,
      auxLists:listDropFrom(BdropY,Ybits,Ybits4Bs),
      xiDragYi(Ybits4Bs, Bbits, Cnf3-Cnf4),!,

      biNajDragCij(Bbits, Abits, Ybits, Ymin, Cnf4-CnfT).

% Xi -> Yi
xiDragYi([X|Xs],[Y|Ys], [[-X,Y]|CnfH]-CnfT):-!,
     xiDragYi(Xs, Ys, CnfH-CnfT).
xiDragYi([],_, Cnf-Cnf):-!.

% Bi & Aj -> Ci+j
biNajDragCij([B|Bs], As, Cs, Cmin, CnfH-CnfT):-!,
       (Cmin > 0 ->
           Cmin1 is Cmin - 1,
           xOrYi(Cmin1,As,B,[A|As2],CnfH-CnfM1),!,
           Cs=[Y|_],
           CnfM1=[[-B,-A,Y],[B,A]|CnfM2],
           bNaiDragCi(As2,Cs,B,CnfM2-CnfM3),!,
           biNajDragCij(Bs,As,Cs,Cmin1,CnfM3-CnfT)
       ;
       (Cs=[_|Ys] ->
           bNaiDragCi(As,Cs,B,CnfH-CnfM),!,
           biNajDragCij(Bs,As,Ys,0,CnfM-CnfT)
       ;
           xDragNotYi(As,B,CnfH-CnfM),!,
           biNajDragCij(Bs,As,[],0,CnfM-CnfT)
       )).
biNajDragCij([], _, _, _, Cnf-Cnf):-!.

xOrYi(0,Ys,_,Ys,Cnf-Cnf):-!.
xOrYi(I,[Y|Ys],X,RYs,[[X,Y]|CnfH]-CnfT):-!,
    I1 is I - 1,
    xOrYi(I1,Ys,X,RYs,CnfH-CnfT).


% B & A1 -> C1 , B & A2 -> C2 ...
% -B & -A1 -> -C1 , -B & -A2 -> -C2 ...
bNaiDragCi([A|As],[C1,C|Cs],B,[[-B,-A, C],[ B, A,-C1]|CnfH]-CnfT):-!,
       bNaiDragCi(As,[C|Cs],B,CnfH-CnfT).
bNaiDragCi([],_,_,Cnf-Cnf):-!.
bNaiDragCi([A|As],[C1],B,[[-B,-A],[B, A,-C1]|CnfH]-CnfT):-!,
       xDragNotYi(As,B,CnfH-CnfT).

xDragNotYi([A|As],B,[[-B,-A]|CnfH]-CnfT):-!,
       xDragNotYi(As,B,CnfH-CnfT).
xDragNotYi([],_,Cnf-Cnf):-!.

:- endif.


:- if(bSettings:unaryAdderType(merger)).
% ---------- Decompose Merger ----------
mergerDecompose(bc(_Type,[A, B, C]),Constrs):-!,
    uadderCnfSimplify(A,B,C,FA,FB,FC),!,
    bcComparator:comparatorType(CompType),
    merger2comparators(FA,FB,FC,CompType,Constrs-[]).

merger2comparators((1,[A]),(1,[B]),Y,CompType,[bc(CompType,[A,B,C,D])|Comps]-Comps):-!,
    ((Y=(0,2,[C,D])) ;
     (Y=(0,1,[C]), D= -1) ;
     (Y=(1,2,[D]), C= 1)).

merger2comparators((Amax,As),(1,[B]),(Ymin,Ymax,Ys),CompType,CompsH-CompsT):-!,
    auxLists:listOddEvenSplit(As,AsOdd,AsEven),
    AOsLen is ceil(Amax / 2),
    AEsLen is Amax - AOsLen,
    CsMax is min(AOsLen+1,ceil((Ymax+1) / 2)),
    createOuput(Ymin,CsMax,Cs),
    combineUnaries(Cs,(0,AEsLen,AsEven),(Ymin,Ymax,Ys),CompType,CompsM-CompsT),!,
    merger2comparators((AOsLen,AsOdd),(1,[B]),Cs,CompType,CompsH-CompsM).

merger2comparators((Amax,As),(Bmax,Bs),(Ymin,Ymax,Ys),CompType,CompsH-CompsT):-!,
    auxLists:listOddEvenSplit(As,AsOdd,AsEven),
    AOsLen is ceil(Amax / 2),
    AEsLen is Amax - AOsLen,

    auxLists:listOddEvenSplit(Bs,BsOdd,BsEven),
    BOsLen is ceil(Bmax / 2),
    BEsLen is Bmax - BOsLen,

    % calculate odd/even outputs
    (Ymin == 0 ->
        Cmin=0,
        Dmin=0
    ;
        Cmin is ceil(Ymin / 2),
        Dmin is floor((Ymin-1)/2)
    ),
    
    Cmax is min(AOsLen+BOsLen,ceil((Ymax+1) / 2)),
    createOuput(Cmin,Cmax,Cs),

    Dmax is min(AEsLen+BEsLen,floor(Ymax / 2)),
    createOuput(Dmin,Dmax,Ds),

    combineUnaries(Cs,Ds,(Ymin,Ymax,Ys),CompType,CompsM-CompsT),!,
    merger2comparators((AEsLen,AsEven),(BEsLen,BsEven),Ds,CompType,CompsH-CompsM1),!,
    merger2comparators((AOsLen,AsOdd),(BOsLen,BsOdd),Cs,CompType,CompsM1-CompsM).

:- endif.



:- if(bSettings:unaryAdderType(hybrid)).
% ---------- Decompose Hybrid ----------
hybridDecompose(bc(_Type,[A, B, C]),Constrs):-!,
    uadderCnfSimplify(A,B,C,FA,FB,FC),!,
    bcComparator:comparatorType(CompType),
    pureUadderType(AdderType),
    decomposeHybrid(FA,FB,FC,CompType,AdderType,Constrs-[]).

pureUadderType([
            bcUnaryAdder:uadderSimplify,
            skipSimplify,
            0,
            bcUnaryAdder:uadder2cnf,
            uadder
           ]).

decomposeHybrid(A,B,Y,CompType,AdderType,ConstrsH-ConstrsT):-
    A=(Amax,Abits),
    B=(Bmax,Bbits),
    Y=(Ymin,Ymax,Ybits),
    uadderCnfSize(Amax,Bmax,Ymin,Ymax,USize),
    hybridCnfSize(Amax,Bmax,Ymin,Ymax,HSize),
    bSettings:unaryAdderHybrid(Factor),
    ((USize =< HSize+Factor ; Bmax==1) ->
        auxUnarynum:unarynumFromList(Abits,FA),
        auxUnarynum:unarynumFromList(Bbits,FB),
        auxUnarynum:unarynumFromList(Ybits,TY),
        auxUnarynum:unarynumAddConst(TY,Ymin,FY),
        /*
        uadder2cnf(bc(_,[FA, FB, FY]), CnfX-[]),
        length(CnfX,CnfXlen),
        (CnfXlen==USize ; writeln((USize,CnfXlen,[Amax,Bmax,Ymin,Ymax]))),
        */
        ConstrsH=[bc(AdderType,[FA,FB,FY])|ConstrsT]
    ;
        /*
        auxUnarynum:unarynumFromList(Abits,FA),
        auxUnarynum:unarynumFromList(Bbits,FB),
        auxUnarynum:unarynumFromList(Ybits,TY),
        auxUnarynum:unarynumAddConst(TY,Ymin,FY),
        uadder2cnf(bc(_,[FA, FB, FY]), CnfX-[]),
        length(CnfX,CnfXlen),
        (CnfXlen==USize ; writeln((USize,CnfXlen,[Amax,Bmax,Ymin,Ymax]))),
        */

        auxLists:listOddEvenSplit(Abits,AsOdd,AsEven),
        AOsLen is ceil(Amax / 2),
        AEsLen is Amax - AOsLen,

        auxLists:listOddEvenSplit(Bbits,BsOdd,BsEven),
        BOsLen is ceil(Bmax / 2),
        BEsLen is Bmax - BOsLen,

        % calculate odd/even outputs
        (Ymin == 0 ->
            Cmin=0,
            Dmin=0
        ;
            Cmin is ceil(Ymin / 2),
            Dmin is floor((Ymin-1)/2)
        ),

        Cmax is min(AOsLen+BOsLen,ceil((Ymax+1) / 2)),
        createOuput(Cmin,Cmax,Cs),

        Dmax is min(AEsLen+BEsLen,floor(Ymax / 2)),
        createOuput(Dmin,Dmax,Ds),

        combineUnaries(Cs,Ds,(Ymin,Ymax,Ybits),CompType,ConstrsM2-ConstrsT),!,
        
        decomposeHybrid((AEsLen,AsEven),(BEsLen,BsEven),Ds,CompType,AdderType,ConstrsH-ConstrsM1),!,
        decomposeHybrid((AOsLen,AsOdd),(BOsLen,BsOdd),Cs,CompType,AdderType,ConstrsM1-ConstrsM2)
    ).

uadderCnfSize(Amax,Bmax,Cmin,Cmax,CnfSize):-
    (Cmin > 1 ->
        DropCnf1 is (Cmin*(Cmin-1))//2
    ;
        DropCnf1 = 0
    ),
    X is Amax + Bmax - 1 - Cmax,
    (X > 0 ->
        CnfSize is 2*(Amax*Bmax + Cmax - Cmin) - (X*(1+X))//2 - DropCnf1
    ;
        CnfSize is 2*(Amax*Bmax + Cmax - Cmin) - DropCnf1
    ).
hybridCnfSize(Amax,Bmax,Cmin,Cmax,CnfSize):-
    (Cmin == 0 ->
        Omin=0,
        Emin=0
    ;
        Omin is ceil(Cmin / 2),
        Emin is floor((Cmin-1)/2)
    ),

    AOsLen is ceil(Amax / 2),
    AEsLen is Amax - AOsLen,
    BOsLen is ceil(Bmax / 2),
    BEsLen is Bmax - BOsLen,

    Omax is min(AOsLen+BOsLen,ceil((Cmax+1) / 2)),
    Emax is min(AEsLen+BEsLen,floor(Cmax / 2)),

    uadderCnfSize(AOsLen,BOsLen,Omin,Omax,CnfSize1),
    uadderCnfSize(AEsLen,BEsLen,Emin,Emax,CnfSize2),
    combineCnfSize(Omin,Omax,Emin,Emax,Cmin,Cmax,CnfSize3),
    CnfSize is CnfSize1 + CnfSize2 + CnfSize3.
    
    
combineCnfSize(Omin,Omax,Emin,Emax,Cmin,Cmax,CnfSize):-
    (Emin==0 ->
        CnfSize is 6*min(min(Omax-1,Emax),Cmax-1)
    ;
        NOmin is Omin - Emin,
        NOmax is Omax - Emin,
        NEmax is Emax - Emin,
        NCmin is Cmin - 2*Emin,
        NCmax is Cmax - 2*Emin,
        combineCnfSize(NOmin,NOmax,0,NEmax,NCmin,NCmax,CnfSize)
    ).

:- endif.


:- if((bSettings:unaryAdderType(merger) ; bSettings:unaryAdderType(hybrid))).

createOuput(Min,Max,(Min,Max,Bits)):-
    Len is Max - Min,
    length(Bits,Len).
createOuput(Val,Val,(Val,Val,[])):-!.


% -------------------------------
% | Unary Combiner As,Bs to Ys  |
% -------------------------------
%% combine two unary numbers to one one unary number (used by mergers)
% it assumes: As>=Bs>=As-2 and |As|=|Bs| |Cs|=|As|+|Bs|
combineUnaries((Amin,Amax,Abits),(Bmin,Bmax,Bbits),(Cmin,Cmax,Cbits),CompType,CompsH-CompsT):-
    (Bmin == 0 ->
        (Amin==0 ->
            (Cmin==0 ; throw(bug(decompose,combineUnaries((Amin,Amax,Abits),(Bmin,Bmax,Bbits),(Cmin,Cmax,Cbits))))),!,
            Abits=[A0|As],
            Cbits=[C0|Cs],
            litUnify(A0,C0),
            combineUnaries_(As,Bbits,Cs,CompType,CompsH-CompsT)
        ;
            (Amin==1 ; throw(bug(decompose,combineUnaries((Amin,Amax,Abits),(Bmin,Bmax,Bbits),(Cmin,Cmax,Cbits))))),!,
            (Cmin==1 ->
                combineUnaries_(Abits,Bbits,Cbits,CompType,CompsH-CompsT)
            ;
                (Cmin==2 ; throw(bug(decompose,combineUnaries((Amin,Amax,Abits),(Bmin,Bmax,Bbits),(Cmin,Cmax,Cbits))))),!,
                combineUnaries_(Abits,Bbits,[1|Cbits],CompType,CompsH-CompsT)
            )
        )
    ;
        NBmax is Bmax - Bmin,
        NAmin is Amin - Bmin,
        NAmax is Amax - Bmin,
        NCmin is Cmin - 2*Bmin,
        NCmax is Cmax - 2*Bmin,
        combineUnaries((NAmin,NAmax,Abits),(0,NBmax,Bbits),(NCmin,NCmax,Cbits),CompType,CompsH-CompsT)
    ).

combineUnaries_([A|As],[B|Bs],[C1,C2|Cs],CompType,[bc(CompType,[A,B,C1,C2])|CompsH]-CompsT):-!,
        combineUnaries_(As,Bs,Cs,CompType,CompsH-CompsT).
combineUnaries_([A],[B],[C1],CompType,[bc(CompType,[A,B,C1,-1])|Comps]-Comps):-!.
combineUnaries_([],[],[],_,Comps-Comps):-!.
combineUnaries_([],[B],[Y],_,Comps-Comps):-!,litUnify(B,Y).
combineUnaries_([A],[],[Y],_,Comps-Comps):-!,litUnify(A,Y).

:- endif.