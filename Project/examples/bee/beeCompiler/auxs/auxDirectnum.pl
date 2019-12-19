% Author: Amit Metodi
% Last Updated: 13/03/2017

:- module(auxDirectnum, [ ]).
:- use_module(auxLists).
:- use_module(auxLiterals).

directnumNewInRange(Min,Max,(Min,Max,Bits,RBits)):-
    (Min==Max -> Bits=[1], RBits=Bits ;
    (Max>Min ->
        Size is Max - Min + 1,
        length(Bits,Size),
        reverse(Bits,RBits)
    ;
        throw(model_err('cannot define direct integer when Min>Max ! ',Min,Max))
    )).

%%% ----- New number Domain -----
directnumNewInDomain(Dom,(Min,Max,Bits,RBits)):-
    Dom=[V0|_],
    (V0= Vmin-Vmin -> Min=Vmin ;
    (V0= Vmin-Vmax -> Vmax > Vmin,!, Min=Vmin ;
    (integer(V0) -> Min=V0 ;
    fail
    ))),
    Min1 is Min - 1,
    domain2direct(Dom,Min1,Max,Bits),
    reverse(Bits,RBits).

directnumNewInDomain(Dom,_):-
    throw(error(invalid_domain(Dom))).

domain2direct([B|Dom],A,Max,Bits):-
   integer(B), B > A, !,
   Len1 is B - A - 1,
   listSplit(Len1,Bits,Falses,RBits1),
   litAsgnFalses(Falses),
   RBits1=[_|RBits2],!,
   domain2direct(Dom,B,Max,RBits2).
domain2direct([B-C|Dom],A,Max,Bits):-
   B < C, B > A, !,
   Len1 is B - A - 1,
   listSplit(Len1,Bits,Falses,RBits1),
   litAsgnFalses(Falses),
   Len2 is C - B + 1,
   listDropFrom(Len2,RBits1,RBits2),
   domain2direct(Dom,C,Max,RBits2).
domain2direct([B-B|Dom],A,Max,Bits):-!,
   domain2direct([B|Dom],A,Max,Bits).
domain2direct([],Max,Max,[]):-!.
        
        
directnumAddConst((Min,Max,Bits),Const,(Min2,Max2,Bits)):-!,
    Min2 is Min + Const,
    Max2 is Max + Const.
    
directnumEquals((Amin,Amax,ADrct,ADrctR),(Bmin,Bmax,BDrct,BDrctR)):-!,
    (Amin==Bmin ->
        litUnifiesWfalses(ADrct,BDrct) ;
    (Amax==Bmax ->
        litUnifiesWfalses(ADrctR,BDrctR) ;
    ((Amin>Bmax ; Bmin>Amax) -> throw(unsat) ;
    (Amin<Bmin ->
        Falses is Bmin - Amin,
        auxLists:listSplit(Falses,ADrct,ADrctF,MADrct),
        litAsgnFalses(ADrctF),
        litUnifiesWfalses(MADrct,BDrct)
    ;
        Falses is Amin - Bmin,
        auxLists:listSplit(Falses,BDrct,BDrctF,MBDrct),
        litAsgnFalses(BDrctF),
        litUnifiesWfalses(MBDrct,ADrct)
    )))).
directnumEquals((Min,Max,Bits,_BitsR),K):-
    integer(K),!,
    ((Min =< K, K =< Max) ->
        Falses1st is K-Min,
        auxLists:listSplit(Falses1st,Bits,F1st,[T|F2nd]),
        litAsgnFalses(F1st),
        litAsgnFalses(F2nd),
        litAsgnTrue(T)
    ;
        throw(unsat)
    ).

directnumNeg((Min,Max,Bits,RBits),(NMin,NMax,RBits,Bits)):-!,
    NMin is -Max,
    NMax is -Min.


directnumDiffK((Min,Max,_,_),K):-
  (K<Min ; K>Max),!.
directnumDiffK((Min,Max,Bits,RBits),K):-
  DropS is K - Min,
  DropE is Max - K,
  (DropS >= DropE ->
      auxLists:listDropFrom(DropS,Bits,[Bi|_])
  ;
      auxLists:listDropFrom(DropE,RBits,[Bi|_])
  ),
  litAsgnFalse(Bi).



%%% ----- Set Max -----

%%% Min > NMax
directnumSetMax((Min,_),NMax,_):-
    NMax < Min,!,
    throw(unsat).
%%% Min=NMax
directnumSetMax((NMax,_,[B0|Bits],_),NMax,(NMax,NMax,[1],[1])):-!,
    litAsgnTrue(B0),
    litAsgnFalses(Bits).
%%% Min < NMax < Max
directnumSetMax((Min,Max,Bits,BitsR),NMax,(Min,NMax,Bits,NBitsR)):-
    NMax < Max,!,
    Drop is Max - NMax,
    auxLists:listSplit(Drop,BitsR,Falses,NBitsR),!,
    litAsgnFalses(Falses).
%%% NMax >= Max
directnumSetMax(Dnum,_,Dnum):-!.


%%% ----- Set Min -----

%%% Min => NMin
directnumSetMin((Min,XXX),NMin,(Min,XXX)):-
    Min >= NMin,!.
%%% Max == NMin
directnumSetMin((_,NMin,_,[Bmax|BitsR]),NMin,(Max,Max,[1],[1])):-!,
    litAsgnTrue(Bmax),
    litAsgnFalses(BitsR).
%%% Min < NMin < Max
directnumSetMin((Min,Max,Bits,BitsR),NMin,(NMin,Max,NBits,BitsR)):-
    Max >= NMin,!,
    Drop is NMin - Min,
    auxLists:listSplit(Drop,Bits,Falses,NBits),!,
    litAsgnFalses(Falses).
%%% NMin > Max
directnumSetMin((_,Max,_),NMin,_):-
    NMin > Max,!,
    throw(unsat).
   

%%% ----- Bounds Changed -----
%%% Assumption: Current Min <= New Min <= New Max <= Current Max
directnumBoundsChanged(Int,Xmin,Xmax,Int,_):-
    Int=(Xmin,Xmax,_),!.
directnumBoundsChanged(X,NMin,NMax,NX,1):-!,
    directnumSetMin(X,NMin,T ),
    directnumSetMax(T,NMax,NX).
   
   
%%% ----- Update number range if needed and mark changed if changed or constant -----
directnumIsChangedOrConst(Int,NInt,Changed):-
    Int=(Min,Max,Bits,BitsR),
    (Min==Max ->
        NInt=Int,
        Changed=1
    ;
    Bits=[Bit0|_],
    BitsR=[Lbit|_],
    ((ground(Bit0) ; ground(Lbit)) ->
        Changed=1,
        directnumFix(Int,NInt)
    ;
        NInt=Int
    )).

directnumFix((Val,Val,_),(Val,Val,[1],[1])):-!.
directnumFix((Min,Max,Bits,BitsR),NNum):-!,
    dropLeadingZeros(Bits,NBits,Min,NMin),
    dropLeadingZeros(BitsR,NBitsR,0,DropR),
    NMax is Max - DropR,
    (NMin < NMax ->
        ((NBits=[B0|MBits], ground(B0), B0=:=1) ->
            litAsgnFalses(MBits),
            NNum=(NMin,NMin,[1],[1]) ;
        ((NBitsR=[Bl|MBits], ground(Bl), Bl=:=1) ->
            litAsgnFalses(MBits),
            NNum=(NMax,NMax,[1],[1]) ;
         NNum=(NMin,NMax,NBits,NBitsR)
         )) ;
    (NMin > NMax -> throw(unsat) ;
    %(NMin == NMax ->
        NBits=[B0|MBits],
        litAsgnTrue(B0),
        litAsgnFalses(MBits),
        NNum=(NMin,NMax,[1],[1])
    )).

dropLeadingZeros(OBits,FBits,SoFar,Droped):-!,
    OBits=[B|Bits],
    ((ground(B),B=:= -1) ->
        SoFar1 is SoFar + 1,
        dropLeadingZeros(Bits,FBits,SoFar1,Droped)
    ;
        FBits=OBits,
        Droped=SoFar
    ).
dropLeadingZeros([],_,_,_):-!, throw(unsat).
