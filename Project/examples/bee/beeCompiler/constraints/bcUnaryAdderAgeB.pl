% Author: Amit Metodi
% Last Updated: 02/02/2012

:- module(bcUnaryAdderAgeB, [ ]).
:- use_module('../auxs/auxLiterals').


%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
uadderAgeBType([
            bcUnaryAdderAgeB:uadderAgeBSimplify1st,
            skipSimplify,
            0,
            0,
            uadderAgeB
           ]).
uadderAgeB2ndType([
            bcUnaryAdderAgeB:uadderAgeBSimplify,
            skipSimplify,
            bcUnaryAdderAgeB:mergerAgeBDecompose,
            0,
            uadderAgeB
           ]).
                   
% --------------------------------
% | Reduce Unary Adder A>=B      |
% --------------------------------
uadderAgeBSimplify1st(bc(_,[A, B, C]), Constr, Changed):-!,
    auxUnarynum:unarynumIsChangedOrConst(A,TA1,Changed),
    auxUnarynum:unarynumIsChangedOrConst(B,TB1,Changed),
    auxUnarynum:unarynumIsChangedOrConst(C,TC1,Changed),!,
    uadderAgeB_fixPosOffsets(TA1,TB1,TC1,TA2,TB2,TC2),!,
    uadderAgeBBoundPropg(TA2,TB2,TC2,NA,NB,NC,DomChanged),
    Changed=DomChanged,
    (specialCases(NA,NB,NC,Constr) ;
     (
      uadderAgeB2ndType(Type),
      Constr=bc(Type,[NA,NB,NC])
    )).


uadderAgeBSimplify(Constr, NewConstr, Changed):-!,
     Constr=bc(Type,[A, B, C]),
     auxUnarynum:unarynumIsChangedOrConst(A,NA,Changed),
     auxUnarynum:unarynumIsChangedOrConst(B,NB,Changed),
     auxUnarynum:unarynumIsChangedOrConst(C,NC,Changed),!,
     (Changed==1 ->
         uadderAgeBBoundPropg(NA,NB,NC,NNA,NNB,NNC,DomChanged),
         (specialCases(NNA,NNB,NNC,NewConstr) ;
         (DomChanged==1 ->
               uadderAgeBSimplify(bc(Type,[NNA,NNB,NNC]), NewConstr, _)
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
   A=(Amin,Amax,Abits,_),
   (Amin==Amax ->
       auxUnarynum:unarynumAddConst(B,Amin,TB),
       auxUnarynum:unarynumEquals(TB,C),
       Constr=none ;
   B=(Bmin,Bmax,Bbits,_),
   (Bmin==Bmax ->
       auxUnarynum:unarynumAddConst(A,Bmin,TA),
       auxUnarynum:unarynumEquals(TA,C),
       Constr=none ;
   (Amin>=Bmax ->
       bcUnaryAdder:uadderSimplify1st(bc(_,[A, B, C]), Constr, _) ;
   C=(Cmin,Cmax,Cbits,_),
   % when Cmin==Cmax then Amin>=Bmax and therefore previous case holds
   ((Abits=[X1], Bbits=[X2]) ->
        ((Amin==Bmin, Amin+Bmin=:=Cmin, Amax+Bmax=:=Cmax) ; throw(bug(simplify,uadderAgeBSpecialSimplify(A,B,C)))),
        Cbits=[Y1,Y2],
        litUnify(X1,Y1),
        litUnify(X2,Y2),
        Constr=none ;
   fail
   )))).
         
% ------------------------------------------------
% | Boundary Propagation for Unary Adder A>=B    |
% ------------------------------------------------
uadderAgeBBoundPropg(A,B,C,NA,NB,NC,DomChanged):-
    A=(Amin,Amax,_),
    B=(Bmin,Bmax,_),
    C=(Cmin,Cmax,_),
        uadderAgeB_propagation_loop((Amin,Amax),(Bmin,Bmax),(Cmin,Cmax),Amm,Bmm,Cmm,DomChanged),!,
        (DomChanged==1 ->
        Amm=(NAmin,NAmax), auxUnarynum:unarynumBoundsChanged(A,NAmin,NAmax,NA,_),
        Bmm=(NBmin,NBmax), auxUnarynum:unarynumBoundsChanged(B,NBmin,NBmax,NB,_),
        Cmm=(NCmin,NCmax), auxUnarynum:unarynumBoundsChanged(C,NCmin,NCmax,NC,_)
        ;
            NA=A, NB=B, NC=C
        ).
        
uadderAgeB_propagation_loop(A,B, Y, FA, FB, FY,Changed):-!,
    uadderAgeB_propagation(A,B,Y,Changed,NA,NB,NY),!,
    (Changed == 1 ->
        uadderAgeB_propagation_loop(NA,NB, NY, FA, FB, FY,_)
    ;
        FA=A, FB=B, FY=Y
    ).
uadderAgeB_propagation(A,B,Y,Changed,NA,NB,NY):-
    A=(Amin,Amax),
    B=(Bmin,Bmax),
    Y=(Ymin,Ymax),
    TAmin is max(Amin,Bmin),
    TBmax is min(Bmax,Amax),
    NYmin is max(TAmin + Bmin, Ymin),
    NYmax is min(Amax + TBmax, Ymax),
        (NYmax>=NYmin ->
    ((Ymin==NYmin, Ymax==NYmax) -> NY=Y ; Changed=1, NY=(NYmin,NYmax))
        ; throw(unsat)),!,
    NAmin is max(TAmin, max(NYmin - TBmax , (NYmin + 1)//2)),
    NAmax is min(Amax, NYmax - Bmin),
        (NAmax>=NAmin ->
    ((NAmin==Amin, NAmax==Amax) -> NA=A ; Changed=1, NA=(NAmin,NAmax))
        ; throw(unsat)),!,
    NBmin is max(Bmin, NYmin - NAmax),
    NBmax is min(TBmax, min(NYmax - NAmin , NYmax // 2)),
        (NBmax>=NBmin ->
    ((NBmin==Bmin, NBmax==Bmax) -> NB=B ; Changed=1, NB=(NBmin,NBmax))
        ; throw(unsat)),!.
        
uadderAgeB_fixPosOffsets((Amin,Amax,Abits),(Bmin,Bmax,Bbits),(Cmin,Cmax,Cbits),(NAmin,NAmax,Abits),(NBmin,NBmax,Bbits),(NCmin,NCmax,Cbits)):-
    MMin is min(min(Amin,Bmin),(Cmin-1)//2),
    NAmin is Amin - MMin,
    NAmax is Amax - MMin,
    NBmin is Bmin - MMin,
    NBmax is Bmax - MMin,
    NCmin is Cmin - 2*MMin,
    NCmax is Cmax - 2*MMin.



% --------------------------
% | Merger A>=B decompose  |
% --------------------------
mergerAgeBDecompose(bc(_Type,[A, B, C]),Constrs):-!,
    uadderAgeBCnfSimplify(A,B,C,FA,FB,FC),!,
    bcComparator:comparatorType(CompType),
    mergerAgeB2comparators(FA,FB,FC,CompType,Constrs-[]).

uadderAgeBCnfSimplify((Amin,Amax,Abits),(Bmin,Bmax,Bbits),(Cmin,Cmax,Cbits),(NAmin,NAmax,Abits),(0,NBmax,Bbits),(NCmin,NCmax,Cbits)):-
    NAmin is Amin - Bmin,
    NAmax is Amax - Bmin,
    NBmax is Bmax - Bmin,
    NCmin is Cmin - 2*Bmin,
    NCmax is Cmax - 2*Bmin.

/*
mergerAgeB2comparators(A,(Bval,Bval,[]),C,_,Comps-Comps):-!,
    A=(Amin,_,Abits),
    C=(Cmin,_,Cbits),
    Offset is Cmin-(Amin+Bval),
    (Offset == 0 ->
         litUnifiesWfalses(Abits,Cbits) ;
    (Offset < 0 ->
         Cones is -Offset,
         auxLists:listSplit(Cones,Cbits,Trues,CRbits),
         litAsgnTrues(Trues),
         litUnifiesWfalses(Abits,CRbits)
    ;
         auxLists:listSplit(Offset,Abits,Trues,ARbits),
         litAsgnTrues(Trues),
         litUnifiesWfalses(ARbits,Cbits)
    )).
*/

mergerAgeB2comparators(A,B,C,CompType,CompsH-CompsT):-!,
    splitOddEven(A,Aodd,Aeven),
    splitOddEven(B,Bodd,Beven),
    createOuput_odd(Aodd,Bodd,C,Codd),
    createOuput_even(Aeven,Beven,C,Ceven),
    combineUnaries(Codd,Ceven,C,CompType,CompsM-CompsT),!,
    uadderAgeBType(UType),
    CompsH=[bc(UType,[Aeven,Beven,Ceven]),
            bc(UType,[Aodd,Bodd,Codd])
            |CompsM].
%    TODO: make recursive calls to work
%    mergerAgeB2comparators(Aeven,Beven,Ceven,CompType,CompsH-CompsM1),!,
%    mergerAgeB2comparators(Aodd,Bodd,Codd,CompType,CompsM1-CompsM).

splitOddEven((Amin,Amax,Abits,_),(AminOdd,AmaxOdd,AbitsOdd,AlastOdd),(AminEven,AmaxEven,AbitsEven,AlastEven)):-
    AminOdd is (Amin+1)//2,
    AmaxOdd is (Amax+1)//2,
    AminEven is Amin//2,
    AmaxEven is Amax//2,
    (AminOdd==AminEven ->
        auxLists:listOddEvenSplit(Abits,AbitsOdd,AbitsEven)
    ;
        auxLists:listOddEvenSplit(Abits,AbitsEven,AbitsOdd)
    ),
    (AminOdd==AmaxOdd -> AlastOdd=1 ; append(_,[AlastOdd],AbitsOdd)),
    (AminEven==AmaxEven -> AlastEven=1 ; append(_,[AlastEven],AbitsEven)).

createOuput_odd((Aomin,Aomax,_),(Bomin,Bomax,_),(Cmin,Cmax,_),Co):-
    Comin is max(Aomin+Bomin, (Cmin+1)//2),
    Comax is min(Aomax+Bomax, ceil((Cmax+1)/2)),
    auxUnarynum:unarynumNewInRange(Comin,Comax,Co).

createOuput_even((Aemin,Aemax,_),(Bemin,Bemax,_),(Cmin,Cmax,_),Ce):-
    Cemin is max(Aemin+Bemin, (Cmin-1)//2),
    Cemax is min(Aemax+Bemax,Cmax//2),
    auxUnarynum:unarynumNewInRange(Cemin,Cemax,Ce).

    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
% -------------------------------
% | Unary Combiner As,Bs to Ys  |
% -------------------------------
%% combine two unary numbers to one one unary number (used by mergers)
% it assumes: As>=Bs>=As-2 and |As|=|Bs| |Cs|=|As|+|Bs|
combineUnaries((Amin,Amax,Abits,_),(Bmin,Bmax,Bbits,_),(Cmin,Cmax,Cbits,_),CompType,CompsH-CompsT):-
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
        combineUnaries((NAmin,NAmax,Abits,_),(0,NBmax,Bbits,_),(NCmin,NCmax,Cbits,_),CompType,CompsH-CompsT)
    ).

combineUnaries_([A|As],[B|Bs],[C1,C2|Cs],CompType,[bc(CompType,[A,B,C1,C2])|CompsH]-CompsT):-!,
        combineUnaries_(As,Bs,Cs,CompType,CompsH-CompsT).
combineUnaries_([A],[B],[C1],CompType,[bc(CompType,[A,B,C1,-1])|Comps]-Comps):-!.
combineUnaries_([],[],[],_,Comps-Comps):-!.
combineUnaries_([],[B],[Y],_,Comps-Comps):-!,litUnify(B,Y).
combineUnaries_([A],[],[Y],_,Comps-Comps):-!,litUnify(A,Y).