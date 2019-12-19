% Author: Amit Metodi
% Last Updated: 22/04/2017

:- module(auxUnarynum, [ ]).
:- use_module(auxLists).
:- use_module(auxLiterals).


%%% ----- New number Range -----

unarynumNewInRange(Min,Max,(Min,Max,Bits,LBit)):-
   (Min==Max -> Bits=[], LBit=1 ;
   (Max>Min ->
       Size is Max - Min,
       createListNlbit(Size,Bits,LBit)
        ;
           throw(model_err('cannot define unary integer when Min>Max ! ',Min,Max))
        )).

createListNlbit(1,[LBit],LBit):-!.
createListNlbit(2,[_,LBit],LBit):-!.
createListNlbit(3,[_,_,LBit],LBit):-!.
createListNlbit(4,[_,_,_,LBit],LBit):-!.
createListNlbit(5,[_,_,_,_,LBit],LBit):-!.
createListNlbit(Size,[_,_,_,_,_|Bits],LBit):-
    Size1 is Size - 5,
    createListNlbit(Size1,Bits,LBit).


%%% ----- New number Domain -----

unarynumNewInDomain([V0|Dom],(Min,Max,Bits,Lbit)):-
   (V0= Vmin-Vmin ->
       Min=Vmin,
       domain2unary(Dom,Vmin,1,Max,Bits,Lbit) ;
   (V0= Vmin-Vmax ->
       Vmax > Vmin,
       Min=Vmin,
       Len is Vmax - Vmin,
       createListNlbit_dl(Len,Bits-RBits,CLbit),
       domain2unary(Dom,Vmax,CLbit,Max,RBits,Lbit) ;
   (integer(V0) ->
       Min=V0,
       domain2unary(Dom,V0,1,Max,Bits,Lbit) ;
   fail
   ))).
unarynumNewInDomain(Dom,_):-
   throw(error(invalid_domain(Dom))).


domain2unary([B|Dom],A,_Pbit,Max,Bits,Lbit):-
   integer(B),!,
   A < B,!,
   Len is B - A,
   listOfmBits(Len,Bits-RBits,X),
   domain2unary(Dom,B,X,Max,RBits,Lbit).
domain2unary([B-C|Dom],A,_Pbit,Max,Bits,Lbit):-
   A < B,
   B < C,!,
   Len1 is B - A,
   listOfmBits(Len1,Bits-RBits1,_),
   Len2 is C - B,
   createListNlbit_dl(Len2,RBits1-RBits2,CLbit),
   domain2unary(Dom,C,CLbit,Max,RBits2,Lbit).
domain2unary([B-B|Dom],A,Pbit,Max,Bits,Lbit):-!,
   domain2unary([B|Dom],A,Pbit,Max,Bits,Lbit).
domain2unary([],Max,Lbit,Max,[],Lbit):-!.


createListNlbit_dl(1,[X|L]-L,X):-!.
createListNlbit_dl(2,[_,X|L]-L,X):-!.
createListNlbit_dl(3,[_,_,X|L]-L,X):-!.
createListNlbit_dl(4,[_,_,_,X|L]-L,X):-!.
createListNlbit_dl(5,[_,_,_,_,X|L]-L,X):-!.
createListNlbit_dl(I,[_,_,_,_,_|LH]-LT,X):-!,
    I5 is I - 5,
    createListNlbit_dl(I5,LH-LT,X).

listOfmBits(1,[X|L]-L,X):-!.
listOfmBits(2,[X,X|L]-L,X):-!.
listOfmBits(3,[X,X,X|L]-L,X):-!.
listOfmBits(4,[X,X,X,X|L]-L,X):-!.
listOfmBits(5,[X,X,X,X,X|L]-L,X):-!.
listOfmBits(I,[X,X,X,X,X|LH]-LT,X):-!,
    I5 is I - 5,
    listOfmBits(I5,LH-LT,X).


%%% ----- New number From list -----
unarynumFromList(Bits,(Min,Max,FBits,LBit)):-
    unarynumFromList_s(Bits,0,Min,Max,FBits,LBit).
    
unarynumFromList_s([X|Xs],Indx,Min,Max,FXs,LBit):-
    ground(X),!,
    (X=:=1 ->
        Indx1 is Indx + 1,
        unarynumFromList_s(Xs,Indx1,Min,Max,FXs,LBit)
    ;
        Min=Indx,
        Max=Min,
        FXs=[],
        LBit=1
    ).
unarynumFromList_s([X|Xs],Indx,Indx,Max,FXs,LBit):-!,
    Indx1 is Indx + 1,
    unarynumFromList_m(Xs,Indx1,Max,X,FXs,LBit).
unarynumFromList_s([],Indx,Indx,Indx,[],1):-!.

unarynumFromList_m([X|Xs],Max,Max,LBit,[LBit],LBit):-
    ground(X), X=:= -1,!,
    litAsgnFalses(Xs).
unarynumFromList_m([X|Xs],Indx,Max,PX,[PX|FXs],LBit):-!,
    Indx1 is Indx + 1,
    unarynumFromList_m(Xs,Indx1,Max,X,FXs,LBit).
unarynumFromList_m([],Indx,Indx,X,[X],X):-!.

%%% ----- Fix number -----

unarynumFix((Val,Val,_,_),(Val,Val,[],1)):-!.
unarynumFix((Min,Max,[B0|Bits],Lbit),(NMin,NMax,NBits,NLbit)):-!,
    (ground(B0) ->
        (B0=:=1 ->
            dropLeadingOnes(Bits,FBits,1,Droped)
        ;
            litAsgnFalse(Lbit),
            FBits=[],
            Droped=0
        )
    ;
        Droped=0,
        FBits=[B0|Bits]
    ),!,
    (ground(Lbit) ->
        (Lbit =:= 1 ->
            NMin=Max,
            NMax=Max,
            NBits=[],
            NLbit=1,
            litAsgnTrues(FBits)
        ;
            NMin is Min + Droped,
            keepLeadingVars(FBits,NBits,Cnt,NLbit),
            NMax is NMin + Cnt
        )
     ;
        NMin is Min + Droped,
        NMax=Max,
        NBits=FBits,
        NLbit=Lbit
     ).

dropLeadingOnes([B|Bits],FBits,SoFar,Droped):-!,
     ((ground(B),B=:=1) ->
          SoFar1 is SoFar + 1,
          dropLeadingOnes(Bits,FBits,SoFar1,Droped)
     ;
          FBits=[B|Bits],
          Droped=SoFar
     ).
dropLeadingOnes([],[],Droped,Droped):-!.

keepLeadingVars([B|FBits],NBits,Cnt,NLbit):-
     (ground(B) ->
         B =:= -1,!,
         Cnt=0,
         NBits=[],
         NLbit=1
     ;
        keepLeadingVars_(FBits,B,NBits,1,Cnt,NLbit)
     ).
keepLeadingVars([],[],0,1):-!.
keepLeadingVars_([B2|Bits],B,[B|NBits],SoFar,Cnt,NLbit):-
     ((ground(B2), B2=:= -1) ->
          NBits=[],
          Cnt=SoFar,
          NLbit=B
     ;
          SoFar1 is SoFar + 1,
          keepLeadingVars_(Bits,B2,NBits,SoFar1,Cnt,NLbit)
     ).
keepLeadingVars_([],B,[B],Cnt,Cnt,B):-!.



%%% ----- Set Max -----

unarynumSetMax(Int,NMax,NInt):-!,
    Int=(Min,Max,Bits,_),
    (NMax < Min -> throw(unsat) ;
    (Min==NMax ->
        litAsgnFalses(Bits),
        NInt=(NMax,NMax,[],1) ;
    (NMax < Max ->
        Keep is NMax - Min,
        unarynumSetMax_(Keep,Bits,NBits,NLBit),
        NInt=(Min,NMax,NBits,NLBit) ;
    NInt=Int
    ))),!.

%unarynumSetMax_(0,Bits,[],1):-!,
%   litAsgnFalses(Bits).
unarynumSetMax_(1,[LB|Bits],[LB],LB):-!,
   litAsgnFalses(Bits).
unarynumSetMax_(2,[B1,LB|Bits],[B1,LB],LB):-!,
   litAsgnFalses(Bits).
unarynumSetMax_(3,[B1,B2,LB|Bits],[B1,B2,LB],LB):-!,
   litAsgnFalses(Bits).
unarynumSetMax_(4,[B1,B2,B3,LB|Bits],[B1,B2,B3,LB],LB):-!,
   litAsgnFalses(Bits).
unarynumSetMax_(5,[B1,B2,B3,B4,LB|Bits],[B1,B2,B3,B4,LB],LB):-!,
   litAsgnFalses(Bits).
unarynumSetMax_(Keep,[B1,B2,B3,B4,B5|Bits],[B1,B2,B3,B4,B5|NBits],NLBit):-!,
   Keep1 is Keep - 5,
   unarynumSetMax_(Keep1,Bits,NBits,NLBit).


%%% ----- Set Min -----

unarynumSetMin(Int,NMin,NInt):-!,
    Int=(Min,Max,Bits,LBit),
    (NMin > Max -> throw(unsat) ;
    (Min >= NMin -> NInt=Int ;
    (NMin==Max ->
        litAsgnTrues(Bits),
        NInt=(NMin,NMin,[],1) ;
    Drop is NMin - Min,
    auxLists:listSplit(Drop,Bits,Trues,NBits),!,
    litAsgnTrues(Trues),
    NInt=(NMin,Max,NBits,LBit)
    ))),!.

%%% ----- Bounds Changed -----
%%% Assumption: Current Min <= New Min <= New Max <= Current Max
unarynumBoundsChanged(X,RXmin,RXmax,NX,Changed):-!,
    (RXmax > RXmin ->
        X=(Xmin,Xmax,Xbits,XLBit),
        ((Xmin==RXmin, Xmax==RXmax) ->
            NX=X
        ;
            Changed=1,
            Drop is RXmin - Xmin,
            auxLists:listSplit(Drop,Xbits,Xtrues,Xbits2),
            litAsgnTrues(Xtrues),!,
            (RXmax==Xmax ->
                NXbits=Xbits2,
                NXLbit=XLBit
            ;
                Size is RXmax - RXmin, % Size >= 1
                auxUnarynum:unarynumSetMax_(Size,Xbits2,NXbits,NXLbit)
            ),!,
            NX=(RXmin,RXmax,NXbits,NXLbit)
        ) ;
    (RXmax==RXmin ->
        X=(Xmin,Xmax,_Xbits,_XLBit),
        ((Xmin==RXmin, Xmax==RXmax) ->
            NX=X
        ;
           Changed=1,
           NX=(RXmin,RXmax,[],1),
           auxUnarynum:unarynumEquals(X,RXmax)
        ) ;
    throw(unsat)
    )).

%%% ----- Focus on sub range -----
%%% Assumption: Dmin<Dmax
unarynumFocusOn(A,Dmin,Dmax,NA):-!,
   A=(Amin,Amax,Abits,ALbit),
   ((Dmin=<Amin,Dmax>=Amax) ->
      NA=A ;
   (Dmin > Amin ->
      Drop is Dmin - Amin,
      NAmin=Dmin,
      auxLists:listDropFrom(Drop,Abits,Abits1)
   ;
      NAmin=Amin,
      Abits1=Abits
   ),!,
   (Amax > Dmax ->
      Keep is Dmax - NAmin,
      keepBits(Keep,Abits1,FAbits,FALbit),
      NA=(NAmin,Dmax,FAbits,FALbit)
   ;
      NA=(NAmin,Amax,Abits1,ALbit)
   )).

unarynumFocusOn(A,Dmin,Dmax,NA,Changed):-!,
   A=(Amin,Amax,Abits,ALbit),
   ((Dmin=<Amin,Dmax>=Amax) ->
      NA=A ;
   Changed=1,
   (Dmin > Amin ->
      Drop is Dmin - Amin,
      NAmin=Dmin,
      auxLists:listDropFrom(Drop,Abits,Abits1)
   ;
      NAmin=Amin,
      Abits1=Abits
   ),!,
   (Amax > Dmax ->
      Keep is Dmax - NAmin,
      keepBits(Keep,Abits1,FAbits,FALbit),
      NA=(NAmin,Dmax,FAbits,FALbit)
   ;
      NA=(NAmin,Amax,Abits1,ALbit)
   )).


keepBits(0, _,[],1):-!.
keepBits(1,[B|_],[B],B):-!.
keepBits(2,[B1,B2|_],[B1,B2],B2):-!.
keepBits(3,[B1,B2,B3|_],[B1,B2,B3],B3):-!.
keepBits(4,[B1,B2,B3,B4|_],[B1,B2,B3,B4],B4):-!.
keepBits(5,[B1,B2,B3,B4,B5|_],[B1,B2,B3,B4,B5],B5):-!.
keepBits(I,[B1,B2,B3,B4,B5|Bs],[B1,B2,B3,B4,B5|RBs],FB):-!,
   I1 is I - 5,
   keepBits(I1,Bs,RBs,FB).

%%% ----- Equals -----
unarynumEquals((Min1,Max1,Bits1,_),(Min2,Max2,Bits2,_)):-
   (Min1==Min2 ->
       litUnifiesWfalses(Bits1,Bits2) ;
   ((Max1<Min2 ; Max2<Min1) -> throw(unsat) ;
   (Min1 > Min2 ->
       Diff is Min1 - Min2,
       auxLists:listSplit(Diff,Bits2,Trues,RBits2),!,
       litAsgnTrues(Trues),
       litUnifiesWfalses(Bits1,RBits2)
   ;
       Diff is Min2 - Min1,
       auxLists:listSplit(Diff,Bits1,Trues,RBits1),!,
       litAsgnTrues(Trues),
       litUnifiesWfalses(RBits1,Bits2)
   ))).
   
unarynumEquals((Min,Max,Bits,_),K):-
   integer(K),!,
   (K==Min ->
      litAsgnFalses(Bits) ;
   (K==Max ->
      litAsgnTrues(Bits) ;
   ((K<Min ; K>Max) ->
      throw(unsat) ;
   Diff is K - Min,
   auxLists:listSplit(Diff,Bits,Trues,Falses),
   litAsgnTrues(Trues),
   litAsgnFalses(Falses)
   ))).

   
%%% ----- A=-B -----
unarynumNeg((Min,Max,Bits,_),(NMin,NMax,RNBits,-B0)):-
   (Bits=[B0|_] ; B0= -1),!,
   litNotReverseXs(Bits,RNBits),
   NMin is -Max,
   NMax is -Min.
   
   
   
%%% ----- Update number range if needed and mark changed if changed or constant -----
unarynumIsChangedOrConst(Int,NInt,Changed):-
    Int=(Min,Max,Bits,Lbit),
    (Min==Max ->
        NInt=Int,
        Changed=1
    ;
    Bits=[Bit1|_],
    ((ground(Bit1) ; ground(Lbit)) ->
        Changed=1,
        unarynumFix(Int,NInt)
    ;
        NInt=Int
    )).
unarynumIsRangeChanged(Int,NInt,Changed):-
    Int=(Min,Max,Bits,Lbit),
    (Min==Max ->
        NInt=Int
    ;
    Bits=[Bit1|_],
    ((ground(Bit1) ; ground(Lbit)) ->
        Changed=1,
        unarynumFix(Int,NInt)
    ;
        NInt=Int
    )).
   
%%% ----- Arithmatics with Constants -----
unarynumAddConst((Min,Max,Bits),Const,(NMin,NMax,Bits)):-!,
  NMin is Min + Const,
  NMax is Max + Const.

unarynumMulByConst(_,0,(0,0,[],1)):-!.
unarynumMulByConst(A,1,A):-!.
unarynumMulByConst(A,-1,NA):-!,
    unarynumNeg(A,NA).
unarynumMulByConst(A,Const,(NMin,NMax,MBits,LBit)):-!,
    (Const > 0 ->
        A=(Min,Max,Bits,LBit),
        NMin is Min * Const,
        NMax is Max * Const,
        mulBits(Const,Bits,Const,MBits)
    ;
       % Const < 0,
       unarynumNeg(A,(Min,Max,Bits,LBit)),
       ConstAbs is -Const,
       NMin is Min * ConstAbs,
       NMax is Max * ConstAbs,
       mulBits(ConstAbs,Bits,ConstAbs,MBits)
    ).


mulBits(0,[_|Bits],Const,MBits):-!,
  mulBits(Const,Bits,Const,MBits).
mulBits(1,[B|Bits],Const,[B|MBits]):-!,
  mulBits(Const,Bits,Const,MBits).
mulBits(2,[B|Bits],Const,[B,B|MBits]):-!,
  mulBits(Const,Bits,Const,MBits).
mulBits(3,[B|Bits],Const,[B,B,B|MBits]):-!,
  mulBits(Const,Bits,Const,MBits).
mulBits(4,[B|Bits],Const,[B,B,B,B|MBits]):-!,
  mulBits(Const,Bits,Const,MBits).
mulBits(5,[B|Bits],Const,[B,B,B,B,B|MBits]):-!,
  mulBits(Const,Bits,Const,MBits).
mulBits(X,[B|Bits],Const,[B,B,B,B,B,B|MBits]):-!,
  X1 is X - 6,
  mulBits(X1,[B|Bits],Const,MBits).
mulBits(_,[],_,[]):-!.

unarynumDivByConst(_,0,_):-!,throw(unsat).
unarynumDivByConst(A,1,A):-!.
unarynumDivByConst(A,-1,NA):-!,
    unarynumNeg(A,NA).
unarynumDivByConst(A,Const,NA):-
    Const < 0,!,
    unarynumNeg(A,NegA),
    NegConst is -Const,
    unarynumDivByConst(NegA,NegConst,NA).
unarynumDivByConst(A,Const,NA):-!,
    Const > 0,!,
    A=(Min,Max,_),
    (Min == Max ->
        Val is Min // Const,
        NA = (Val,Val,[],1) ;
    (Min >= 0 ->
        unarynumDivByConst_pos(A,Const,NA) ;
    (Max =< 0 ->
        unarynumNeg(A,NegA),
        unarynumDivByConst_pos(NegA,Const,NegNA),
        unarynumNeg(NegNA,NA) ;
    unarynumDivByConst_mix(A,Const,NA)
    ))).

unarynumDivByConst_pos(A,Const,NA):-!,
    A=(Min,Max,Bits,_),
    NMin is Min // Const,
    NMax is Max // Const,
    (NMin < NMax ->
        Drop is Const - Min mod Const - 1,
        Const1 is Const - 1,
        auxLists:listDropFrom(Drop,Bits,Bits1),!,
        keepIthBits(Bits1,Const1,DBits,DLBit),
        NA=(NMin,NMax,DBits,DLBit)
    ;
        NA=(NMin,NMax,[],1)
    ).
unarynumDivByConst_mix(A,Const,NA):-!,
    A=(Min,Max,Bits,_),
    Const1 is Const - 1,
    SplitSz is -Min,
    auxLists:listSplit(SplitSz,Bits,BitsNeg,BitsPos),
    (auxLists:listDropFrom(Const1,BitsPos,BitsPosM) ->
        keepIthBits(BitsPosM,Const1,NBitsPos,_)
    ;
        NBitsPos=[]
    ),
    (SplitSz >= Const ->
        reverse(BitsNeg,BitsNegR),
        auxLists:listDropFrom(Const1,BitsNegR,BitsNegRM),
        keepIthBits(BitsNegRM,Const1,NBitsNegR,_),
        reverse(NBitsNegR,NBitsNeg)
    ;
        NBitsNeg=[]
    ),!,
    append(NBitsNeg,NBitsPos, NBits),
    (NBits = [] ->
        LBit=1
    ;
        append(_,[LBit],NBits)
    ),!,
    NMin is Min // Const,
    NMax is Max // Const,
    NA=(NMin,NMax,NBits,LBit).

    

keepIthBits([X|Xs],Drop,[X|DBits],DLBit):-!,
    (auxLists:listDropFrom(Drop,Xs,RXs) ->
        (RXs=[_|_] ->
            keepIthBits(RXs,Drop,DBits,DLBit)
        ;
            DBits=[],
            DLBit=X
        )
    ;
        DBits=[],
        DLBit=X
    ).
keepIthBits([],_Drop,[],1):-!.


%% (A >= K) <-> Z
unarynumGEqK((Min,Max,Bits,Lbit),K,Z):-
  (K =< Min -> litAsgnTrue(Z) ;
  (K > Max -> litAsgnFalse(Z) ;
  (K == Max -> litUnify(Lbit,Z) ;
  Indx is K - Min,
  nth1(Indx,Bits,T),
  litUnify(T,Z)
  ))).

unarynumDiffK((Min,Max,_,_),K):-
  (K<Min ; K>Max),!.
unarynumDiffK((Min,Max,Bits,Lbit),K):-
%  (Min==Max -> throw(unsat) ;
  (Max==K -> litAsgnFalse(Lbit) ;
  (Min==K -> Bits=[B0|_], litAsgnTrue(B0) ;
  Drop is K - Min - 1,
  auxLists:listDropFrom(Drop,Bits,[B0,B1|_]),
  litUnify(B0,B1)
  )).
