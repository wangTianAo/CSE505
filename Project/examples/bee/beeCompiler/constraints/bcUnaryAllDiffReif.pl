% Author: Amit Metodi
% Last Update: 19/09/2015

:- module(bcUnaryAllDiffReif, [ ]).
:- use_module('../auxs/auxLiterals').

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%

:- Head=int_array_allDiff_reif(Ints,Reif,ConstrsH-ConstrsT),
   Body=(
       !,
       bcInteger:getUnaryNumbers(Ints,Intsu),
       bcInteger:getDirectNumbers(Ints,Intsd),
       bcUnaryAllDiffReif:unaryAllDiffReifType(Type),
       Data=[Reif,Intsd,Intsu,[]],
       ConstrsH=[bc(Type,Data)|ConstrsT]
   ),
   bParser:addConstraint(Head,Body).
   
%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
unaryAllDiffReifType([
            bcUnaryAllDiffReif:unaryAllDiffReifSimplify,
            skipSimplify,
            bcUnaryAllDiffReif:unaryAllDiffReifDecompose,
            0,
            unaryAllDiffReif
           ]).


% --------------------------------
% | Simplify                     |
% --------------------------------
unaryAllDiffReifSimplify(OldConstr,NewConstr,Changed):-!,
    OldConstr=bc(Type,[Reif,NumDs,NumUs,NumCs]),
    ((ground(Reif), Reif =:= 1) ->
        Changed=1,
        (NumCs==[] ; numsDiffConsts(NumDs,NumUs,NumCs)),!,
        convertToAllDiff(NumDs,NumUs,NewConstr)
    ;
        unaryAllDiffReifSimplify_aux(NumDs,NumUs,NNumDs,NNumUs,NNumCs,Changed),
        (Changed==1 ->
            (NNumCs==[] ->
                NewConstr=bc(Type,[Reif,NNumDs,NNumUs,NumCs])
            ;
                msort(NNumCs,SNumCs),!,
                mergeConstants(SNumCs,NumCs,FNumCs,NotDiff),!,
                (NotDiff==1 ->
                    litAsgnFalse(Reif),
                    NewConstr=none ;
                (NNumDs==[] ->
                     litAsgnTrue(Reif),
                     NewConstr=none ;
                (NNumDs==[D1] ->
                     D1=(Min,_,D1Bits,_),
                     collectSpecificBits(FNumCs,Min,D1Bits,Bits),
                     bcOr:orType(OrType),
                     auxLiterals:lits2plits(Bits,OrVec),
                     bcOr:orSimplify(bc(OrType,[-Reif|OrVec]),NewConstr,_)
                ;
                    NewConstr=bc(Type,[Reif,NNumDs,NNumUs,FNumCs])
                )))
            )
        ;
            NewConstr=OldConstr
        )
    ).


unaryAllDiffReifSimplify_aux([D|Ds],[U|Us],NDs,NUs,NCs,Changed):-!,
   simplifyDirect(D,ND,Droped,Fixed),
   (Fixed==1 ->
       Changed=1,
       ND=(Min,_),
       NCs=[Min|MCs],
       unaryAllDiffReifSimplify_aux(Ds,Us,NDs,NUs,MCs,Changed) ;
   (Droped==0 ->
       NDs=[D|MDs],
       NUs=[U|MUs]
   ;
       Changed=1,
       simplifyUnary(U,Droped,NU),
       NDs=[ND|MDs],
       NUs=[NU|MUs]
   ),
   unaryAllDiffReifSimplify_aux(Ds,Us,MDs,MUs,NCs,Changed)).
unaryAllDiffReifSimplify_aux([],[],[],[],[],_):-!.

simplifyDirect(D,ND,Droped,Fixed):-
   D=(Min,Max,Bits,RBits),
   auxDirectnum:dropLeadingZeros(Bits,FBits,0,Droped),
   (Droped==0 ->
       ND=D ;
   Min1 is Min + Droped,
   ((FBits=[NBit|MBits], ground(NBit), NBit=:=1) ->
       Fixed = 1,
       litAsgnFalses(MBits),
       ND=(Min1,Min1,[1],[1])
   ;
       ND=(Min1,Max,FBits,RBits)
   )).

simplifyUnary((Min,Max,Bits,LBit),Droped,NU):-
   auxLists:listSplit(Droped,Bits,TBits,RBits),
   litAsgnTrues(TBits),
   (RBits==[] ->
       NU=(Max,Max,[],1)
   ;
       MinF is Min + Droped,
       NU=(MinF,Max,RBits,LBit)
   ).

mergeConstants(NCs,OCs,Result,NotDiff):-!,
    (NCs==[] ->
        Result=OCs ;
    NCs=[NC|MNCs],
    (OCs==[] ->
        mergeConstants(MNCs,[NC],Result,NotDiff) ;
    OCs=[OC|MOCs],
    (OC==NC ->
        NotDiff=1 ;
    (OC<NC ->
        Result=[OC|RResult],
        mergeConstants(NCs,MOCs,RResult,NotDiff) ;
    %% OC>NC
        mergeConstants(MNCs,[NC|OCs],Result,NotDiff)
    )))).
    

collectSpecificBits([],_,_,[]):-!.
collectSpecificBits([C|Cs],Min,Dbits,Bits):-
    C<Min,!,
    collectSpecificBits(Cs,Min,Dbits,Bits).
collectSpecificBits([C|Cs],Min,Dbits,Bits):-
    Drop is C - Min,
    (auxLists:listDropFrom(Drop,Dbits,[B|RDbits]) ->
        Bits=[B|MBits],
        Min1 is C + 1,
        collectSpecificBits(Cs,Min1,RDbits,MBits)
    ;
        Bits=[]
    ).

numsDiffConsts([D|NumDs],[U|NumUs],NumCs):-!,
    numsDiffConsts_aux(NumCs,U,D),
    numsDiffConsts(NumDs,NumUs,NumCs).
numsDiffConsts([],[],_):-!.

numsDiffConsts_aux([C|NumCs],U,D):-
    auxUnarynum:unarynumDiffK(U,C),!,
    auxDirectnum:directnumDiffK(D,C),!,
    numsDiffConsts_aux(NumCs,U,D).
numsDiffConsts_aux([],_,_):-!.

convertToAllDiff(NumDs,NumUs,Constr):-!,
    combineNumsForAllDiff(NumDs,NumUs,FInts),
    msort(FInts,SFInts),
    bcUnaryAllDiff:addNumbers2DataStructs(SFInts,1,Buckets,Numbers),
    length(Buckets,BCnt),
    length(Numbers,NCnt),!,
    (BCnt<NCnt -> throw(unsat) ;
    (BCnt==NCnt ->
        bcUnaryAllDiff:unaryPermutationType(Type),
        Constr=bc(Type,[Buckets,Numbers])
    ;
        bcUnaryAllDiff:unaryAllDiffType(Type),
        Constr=bc(Type,[Buckets,Numbers,(BCnt,NCnt)])
    )).

combineNumsForAllDiff([D|Ds],[O|Os],[R|Rs]):-!,
    O=(Min,Max,OBits,_),
    D=(Min,Max,DBits,_),
    R=(Min,DBits,OBits),!,
    combineNumsForAllDiff(Ds,Os,Rs).
combineNumsForAllDiff([],[],[]):-!.


% --------------------------------
% | Decompose                    |
% --------------------------------
unaryAllDiffReifDecompose(bc(_Type,[Reif,NumDs,_NumUs,NumCs]),Constrs):-!,
    bcDirectRels:directNeqReifType(DiffType),
    eqPairsReif(NumDs,DiffType,Reifs-ReifsT,Constrs-Constrs2),
    (NumCs==[] ->
        ReifsT=[]
    ;
        eqConstsBits(NumDs,NumCs,EqBits),
        flatten(EqBits,ReifsT)
    ),!,
    bcOr:orType(OrType),
    auxLiterals:lits2plits(Reifs,OrVec),
    Constrs2=[bc(OrType,[-Reif|OrVec])].
    
eqPairsReif([D|Ds],DiffType,ReifsH-ReifsT,ConstrsH-ConstrsT):-!,
    eqPairsReif_aux(Ds,D,DiffType,ReifsH-ReifsM,ConstrsH-ConstrsM),!,
    eqPairsReif(Ds,DiffType,ReifsM-ReifsT,ConstrsM-ConstrsT).
eqPairsReif([],_,Reifs-Reifs,Constrs-Constrs):-!.

eqPairsReif_aux([Di|Ds],D1,DiffType,ReifsH-ReifsT,ConstrsH-ConstrsT):-
    D1=(D1min,D1max,_),
    Di=(Dimin,Dimax,_),
    ((D1min>Dimax ; Dimin>D1max) ->
        eqPairsReif_aux(Ds,D1,DiffType,ReifsH-ReifsT,ConstrsH-ConstrsT)
    ;
        ReifsH=[-Df|ReifsM],
        ConstrsH=[bc(DiffType,[Df,D1,Di])|ConstrsM],
        eqPairsReif_aux(Ds,D1,DiffType,ReifsM-ReifsT,ConstrsM-ConstrsT)
    ).
eqPairsReif_aux([],_,_,Reifs-Reifs,Constrs-Constrs):-!.

eqConstsBits([(Min,_,DBits,_)|Ds],NumCs,[DEqBits|EqBits]):-!,
    collectSpecificBits(NumCs,Min,DBits,DEqBits),
    eqConstsBits(Ds,NumCs,EqBits).
eqConstsBits([],_,[]):-!.