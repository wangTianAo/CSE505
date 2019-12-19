% Author: Amit Metodi
% Last Updated: 25/04/2016

:- module(bcUnaryMod, [ ]).
:- use_module('../auxs/auxLiterals').


%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=int_mod(A,B,C,ConstrsH-ConstrsT),
   Body=(
       !,
       bcInteger:getUnaryNumber(A,Au),
       bcInteger:getUnaryNumber(B,Bu),
       bcInteger:getUnaryNumber(C,Cu),
       auxUnarynum:unarynumDiffK(Bu,0),
       auxUnarynum:unarynumIsRangeChanged(Au,Au2,_),
       auxUnarynum:unarynumIsRangeChanged(Bu,Bu2,_),
       auxUnarynum:unarynumIsRangeChanged(Cu,Cu2,_),
       bcUnaryMod:unaryModDecompose(Au2,Bu2,Cu2,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).



unaryModDecompose(A,B,C,ConstrsH-ConstrsT):-
    bcUnaryMax:unaryMaxType(MaxType),
    %%% Step 1 - get Aabs=abs(A), Babs=abs(B), Cabs=abs(C)
    % Get A pos and neg
    getABSnumber(A,Aabs,Alt0,Agt0,MaxType,ConstrsH-ConstrsM1),!,
    % Get B pos and neg
    getABSnumber(B,Babs,Blt0,Bgt0,MaxType,ConstrsM1-ConstrsM2),!,
    % Get C pos and neg
    getABSnumber(C,Cabs,Clt0,Cgt0,MaxType,ConstrsM2-ConstrsM3),!,
    % Step 2 - calculate |A| mod |B| = |C|
    bcUnaryMod:unaryPosModType(ModType),
    unaryModPosSimplify(bc(ModType,[Aabs,Babs,Cabs]),ModConstr,1),
    (ModConstr==none ->
        ConstrsM3=ConstrsM4
    ;
        ConstrsM3=[ModConstr|ConstrsM4]
    ),!,
    % Step 3 - set Signs
    bcAtLeastOne:aloType(ALOType),
    auxLiterals:lits2plits([-Agt0,-Bgt0,-Clt0],OrVec1),
    auxLiterals:lits2plits([-Alt0,-Blt0,-Clt0],OrVec2),
    auxLiterals:lits2plits([-Agt0,-Blt0,-Cgt0],OrVec3),
    auxLiterals:lits2plits([-Alt0,-Bgt0,-Cgt0],OrVec4),
    ConstrsM4=[
              bc(ALOType,OrVec1),
              bc(ALOType,OrVec2),
              bc(ALOType,OrVec3),
              bc(ALOType,OrVec4)
              |ConstrsT].


getABSnumber(A,Aabs,Alt0,Agt0,MaxType,ConstrsH-ConstrsT):-
    A=(Amin,Amax,_),
    (Amin >= 0 -> % Possitive
        Alt0= -1,
        (Amin>0 ->
            Agt0=1
        ;
            (A=(_,_,[Agt0|_],_) ; Agt0= -1)
        ),
        Aabs=A,
        ConstrsH=ConstrsT
    ;
    (Amax =<0 ->
        Agt0= -1,
        (Amax < 0 ->
            Alt0=1
        ; % Amax==0
            A=(_,_,_,NAlt0),
            Alt0= -NAlt0
        ),
        auxUnarynum:unarynumNeg(A,Aabs),
        ConstrsH=ConstrsT
    ;
        bcUnaryAbs:splitUnaryNumToPosNeg(A,Apos,Aneg),
        Apos=(_,Amax1,[Agt0|_],_),
        Aneg=(_,Amax2,[Alt0|_],_),
        AabsMax is max(Amax1,Amax2),
        auxUnarynum:unarynumNewInRange(0,AabsMax,Aabs),
        ConstrsH=[bc(MaxType,[Aabs,Apos,Aneg])|ConstrsT]
    )).


%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
unaryPosModType([
                 bcUnaryMod:unaryModPosSimplify,
                 skipSimplify,
                 bcUnaryMod:unaryModPosDecompose,
                 0,
                 unaryPosMod]).

% --------------------------------------
% | Simplify  A mod B = C  (A,B,C >=0) |
% --------------------------------------
unaryModPosSimplify(Constr,NewConstr,Changed):-!,
    Constr=bc(Type,[A,B,C]),
    auxUnarynum:unarynumIsRangeChanged(A,FA,Changed),
    auxUnarynum:unarynumIsChangedOrConst(B,FB,Changed),
    auxUnarynum:unarynumIsRangeChanged(C,FC,Changed),
    (Changed==1 ->
        modSimplify_prop(FA,FB,FC,Type,NewConstr)
    ;
        NewConstr=Constr
    ).

modSimplify_prop(A,B,C,Type,Constr):-!,
    B=(Bmin,Bmax,_),
    (Bmin==Bmax ->
        (Bmax==1 -> % A mod 1 = 0
            Constr=none,
            auxUnarynum:unarynumEquals(C,0)
        ;
            unaryPosModKType(ModKType),
            modKSimplify_prop(A,Bmin,C,ModKType,Constr)
        ) ;
    A=(Amin,Amax,_),
    C=(Cmin,Cmax,_),
    (Cmin > Amin ->
        auxUnarynum:unarynumSetMin(A,Cmin,FA),
        modSimplify_prop(FA,B,C,Type,Constr) ;
    (Cmax > Amax ->
        auxUnarynum:unarynumSetMax(C,Amax,FC),
        modSimplify_prop(A,B,FC,Type,Constr) ;
    (Amax < Bmin -> % (A mod B = C) where Amax<Bmin then A=C
        Constr=none,
        auxUnarynum:unarynumEquals(A,C) ;
    (Amax+1 < Bmax ->
        NewBmax is Amax + 1,
        auxUnarynum:unarynumFocusOn(B,Bmin,NewBmax,FB),
        modSimplify_prop(A,FB,C,Type,Constr) ;
    (Cmin >= Bmin ->
        NBmin is Cmin + 1,
        auxUnarynum:unarynumSetMin(B,NBmin,FB),
        modSimplify_prop(A,FB,C,Type,Constr) ;
    (Cmax >= Bmax ->
        NCmax is Bmax - 1,
        auxUnarynum:unarynumSetMax(C,NCmax,FC),
        modSimplify_prop(A,B,FC,Type,Constr) ;
    Constr=bc(Type,[A,B,C])
    ))))))).

% ---------------------------------------
% | Decompose  A mod B = C  (A,B,C >=0) |                  |
% ---------------------------------------
unaryModPosDecompose(bc(_Type,[A,B,C]),Constrs):-!,
    A=(_,Amax,_),
    C=(_,Cmax,_),

    bcSorted:sortedType(SortType),

    % Y = A - C
    Ymin is -Cmax,
    auxUnarynum:unarynumNewInRange(Ymin,Amax,Yu),
    Yu=(_,_,YBits,_),
    
    bcUnaryAdder:uadderSimplify1st(bc(_,[Yu, C, A]), AddConstr, _),
    (AddConstr==none ->
        Constrs=[bc(SortType,YBits)|Constrs1]
    ;
        Constrs=[bc(SortType,YBits),AddConstr|Constrs1]
    ),!,

    % X = A / B
    % B * X = Y
    Xmin is -Cmax,
    auxUnarynum:unarynumNewInRange(Xmin,Amax,Xu), %% TODO better range
    Xu=(_,_,XBits,_),

    bcUnaryTimes:utimesType(TimesType),
    bcUnaryTimes:utimesSimplify(bc(TimesType,[B, Xu, Yu]), ConstrTimes, 1),
    (ConstrTimes==none ->
        Constrs1=[bc(SortType,XBits)|Constrs2]
    ;
        Constrs1=[bc(SortType,XBits),ConstrTimes|Constrs2]
    ),!,

    bcUnaryDiv:udivType(DivType),
    bcUnaryDiv:udivSimplify(bc(DivType,[A, B, Xu]), ConstrDiv, 1),
    (ConstrDiv==none ->
        Constrs2=[]
    ;
        Constrs2=[ConstrDiv]
    ).


%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
unaryPosModKType([
                 bcUnaryMod:unaryModKPosSimplify,
                 skipSimplify,
                 bcUnaryMod:unaryModKPosDecompose,
                 0,
                 unaryPosModK]).


%%% ----------------------------------------- %%%
%%% | Simplify  (A mod K == C)  (A,K,C >=0) | %%%
%%% ----------------------------------------- %%%
unaryModKPosSimplify(Constr,NewConstr,Changed):-
    Constr=bc(Type,[A,K,C]),
    auxUnarynum:unarynumIsRangeChanged(A,FA,Changed),
    auxUnarynum:unarynumIsRangeChanged(C,FC,Changed),
    (Changed==1 ->
        modKSimplify_prop(FA,K,FC,Type,NewConstr)
    ;
        NewConstr=Constr
    ).

modKSimplify_prop(A,K,C,ModKType,NewConstr):-!,
    A=(Amin,Amax,_),
    (Amin==Amax -> % (K1 mod K2 = C) -> C is K1 mod K2
        AmodK is Amin mod K,
        NewConstr=none,
        auxUnarynum:unarynumEquals(C,AmodK) ;
    (Amax < K ->
        NewConstr=none,
        auxUnarynum:unarynumEquals(A,C) ;
    (Amin>=K ->  % Example: [5..10] mod 3 = C  -> [2..7] mod 3 = C
        ReduceA is -(Amin - (Amin mod K)),
        auxUnarynum:unarynumAddConst(A,ReduceA,FA),
        modKSimplify_prop(FA,K,C,ModKType,NewConstr) ;
    C=(Cmin,Cmax,_),
    (Cmax>=K ->
        K1 is K - 1,
        auxUnarynum:unarynumSetMax(C,K1,FC),
        modKSimplify_prop(A,K,FC,ModKType,NewConstr) ;
    (Cmin > Amin ->
        auxUnarynum:unarynumSetMin(A,Cmin,FA),
        modKSimplify_prop(FA,K,C,ModKType,NewConstr) ;
    % Reduce A maximum value according to C
    Xval is (Amax mod K) - Cmax,
    (Xval > 0 -> % Example: (0..20) mod 7 = (0..4) >>> (0.. 18) mod 7 = (0..4)
        NewAmax is Amax - Xval,
        auxUnarynum:unarynumSetMax(A,NewAmax,FA),
        modKSimplify_prop(FA,K,C,ModKType,NewConstr) ;
    (Cmin==Cmax ->
        NewConstr=none,
        modSimplify_removeValsA(A,K,Cmin,Cmax) ;
    ((Cmin>0 ; Cmax+1<K) ->
        modSimplify_removeValsA(A,K,Cmin,Cmax),
        NewConstr=bc(ModKType,[A,K,C]) ;
    NewConstr=bc(ModKType,[A,K,C])
    )))))))).

% Amin >= Cmin
modSimplify_removeValsA(A,Bval,Cmin,Cmax):-
    A=(Amin,_Amax,Abits,_),
    !, Amin >= Cmin, !, % assert
    Drop1st is Cmax - Amin,
    (Drop1st<0 ->
        L is -Drop1st,length(OL,L),auxLiterals:litAsgnTrues(OL),append(OL,Abits,Abits1)
    ;
        auxLists:listDropFrom(Drop1st,Abits,Abits1)
    ),
    NoChange is Cmax - Cmin,
    Unifies is Bval - NoChange,
    modSimplify_removeValsA_uni(Abits1,NoChange,Unifies).

modSimplify_removeValsA_uni(Xs,NoChange,Unifies):-!,
    (auxLists:listSplit(Unifies,Xs,[Uto|UPart],Xs1) ->
        unifyTo(UPart,Uto),
        (auxLists:listDropFrom(NoChange,Xs1,Xs2) ->
            modSimplify_removeValsA_uni(Xs2,NoChange,Unifies)
        ;
            true
        )
    ;
        auxLiterals:litAsgnFalses(Xs)
    ).

unifyTo([X|Xs],Y):-!,
    auxLiterals:litUnify(X,Y),
    unifyTo(Xs,Y).
unifyTo([],_):-!.

%%% ------------------------------------------ %%%
%%% | Decompose  (A mod K == C)  (A,K,C >=0) | %%%
%%% ------------------------------------------ %%%

unaryModKPosDecompose(bc(_Type,[A,K,C]),Constrs):-!,
    unaryModKPosDecompose_aux(A,K,C,Constrs).


:- if(bSettings:unaryMod2decompose(xor)). % define xorReif2cnf predicate based on bSettings
% A mod 2 = C
unaryModKPosDecompose_aux(A,2,C,Constrs):-!,
    % assert C=[0..1]
    C=(0,1,_,CXorBit),
    A=(Amin,_,AXorBits,_),
    (Amin mod 2 =:= 0 ->
        lits2plits([-CXorBit|AXorBits],XOrVec)
    ;
        lits2plits([CXorBit|AXorBits],XOrVec)
    ),
    bcXor:xorType(XORType),
    Constrs=[bc(XORType,XOrVec)].
:- endif.

% A mod k = C where Amin<k , Amax>=k
unaryModKPosDecompose_aux(A,K,C,Constrs):-!,
    A=(Amin,Amax,AbitsO,_),
    C=(Cmin,Cmax,Cbits,_),
    % asset
    !,Cmin=<Amin,

    PadA is Amin - Cmin,
    auxLists:listSplit(PadA,Abits,Abits1s,AbitsO),
    auxLiterals:litAsgnTrues(Abits1s),!,

    Keep is Cmax - Cmin,
    Drop1 is Cmin,
    Drop2 is K - Cmax - 1,

    splitUnaryToParts(Abits,Keep,Drop2,Drop1,UParts,UIndx),

    CntParts is Amax // K + 1,
    (CntParts==2 ->
        UParts=[Vec1,Vec2],
        UIndx=[I],
        bcITE:iteReifType(ITEtype),
        createModMux_ite(Vec1,Vec2,I,Cbits,ITEtype,Constrs)
    ;
        matrixTranspose(UParts,UPartsTr),!,
        bcBoolElement:boolElementType(BElType),!,
        length(DIndx, CntParts),
        bcUnaryDirectChnl:chnlU2DType(ChnlType),
        auxLiterals:lits2plits(DIndx,DIndxPB),
        Constrs=[bc(ChnlType,[UIndx,DIndx,DIndxPB])|Constrs2],
        createModMux(UPartsTr,DIndx,Cbits,BElType,Constrs2)
    ).

splitUnaryToParts(Abits,Keep,DropAfter,DropBefore,UParts,UIndx):-
    (auxLists:listSplit(Keep,Abits,UPart,Abits1) ->
        UParts=[UPart|MUParts],
        (auxLists:listDropFrom(DropAfter,Abits1,[I|Abits2]) ->
            UIndx=[I|MUIndx],
            (auxLists:listDropFrom(DropBefore,Abits2,Abits3) ->
                splitUnaryToParts(Abits3,Keep,DropAfter,DropBefore,MUParts,MUIndx)
            ;
                length(Empty,Keep),
                auxLiterals:litAsgnFalses(Empty),
                MUParts=[Empty],
                MUIndx=[]
            )
        ;
            MUParts=[],
            UIndx=[]
        )
    ;
        extendsWithFalses(Keep,Abits,FixAbits),
        UParts=[FixAbits],
        UIndx=[]
    ).

extendsWithFalses(0,Xs,Xs):-!.
extendsWithFalses(I,[Xi|Xs],[Xi|NXs]):-!,
    I1 is I - 1,
    extendsWithFalses(I1,Xs,NXs).
extendsWithFalses(I,[],NXs):-!,
    length(NXs,I),!,
    auxLiterals:litAsgnFalses(NXs).


% matrixTranspose_null(Mtrx,MtrxTr)
matrixTranspose(Rows,[]) :-
        matrixTranspose_null(Rows).
matrixTranspose(Rows,[FirstCol|Cols]) :-
        matrixTranspose_row(Rows,FirstCol,RestRows),
        matrixTranspose(RestRows,Cols).

matrixTranspose_row([],[],[]).
matrixTranspose_row([[X|RestRow]|Rows],[X|Col],[RestRow|RestRows]) :-
        matrixTranspose_row(Rows,Col,RestRows).

matrixTranspose_null([]).
matrixTranspose_null([[]|Ns]) :-
        matrixTranspose_null(Ns).

createModMux([Vec|Vecs],Indx,[Out|Output],BElType,[bc(BElType,[Indx,Vec,Out])|Constrs]):-!,
    createModMux(Vecs,Indx,Output,BElType,Constrs).
createModMux([],_,[],_,[]):-!.

createModMux_ite([V1|Vec1],[V2|Vec2],I,[O|Output],ITEtype,[bc(ITEtype,[I,V2,V1,O])|Constrs]):-!,
    createModMux_ite(Vec1,Vec2,I,Output,ITEtype,Constrs).
createModMux_ite([],[],_,[],_,[]):-!.