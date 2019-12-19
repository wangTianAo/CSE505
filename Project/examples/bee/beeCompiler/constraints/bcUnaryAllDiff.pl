% Author: Amit Metodi
% Last Updated: 05/09/2016

:- module(bcUnaryAllDiff, [ ]).
:- use_module('../auxs/auxLiterals').

/*
 Data Stuctures:
   1. Numbers: [(NID,Min,Drct),...]
   2. Buckets: [[BVal,(Dl,Dop,NID,U0,U1),...],...]
*/

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- if(bSettings:allDiffDecompose(dual)).

:- Head=int_array_allDiff(Ints,ConstrsH-ConstrsT),
   Body=(
       !,
       ((Ints=[] ; Ints=[_]) ->
            ConstrsH=ConstrsT ;
%       (Ints=[A,B] ->
%            bcInteger:getUnaryNumber(A,Au),
%            bcInteger:getUnaryNumber(B,Bu),
%            bcUnaryDiff:newUnaryDiff(Au,Bu,ConstrsH-ConstrsT) ;
       bcUnaryAllDiff:createDataStructs(Ints,Buckets,Numbers),
       length(Buckets,BCnt),
       length(Numbers,NCnt),
       (BCnt<NCnt -> throw(unsat) ;
%       bcUnaryAllDiff:split2diffs(Ints,ConstrsM-ConstrsT),
       (BCnt==NCnt ->
           bcUnaryAllDiff:unaryPermutationType(Type),
           ConstrsH=[bc(Type,[Buckets,Numbers])|ConstrsT]
      ;
           bcUnaryAllDiff:unaryAllDiffType(Type),
           ConstrsH=[bc(Type,[Buckets,Numbers,(BCnt,NCnt)])|ConstrsT]
       )))
%       )
   ),
   bParser:addConstraint(Head,Body).
   
:- elif(bSettings:allDiffDecompose(pairwise)).

:- Head=int_array_allDiff(Ints,ConstrsH-ConstrsT),
   Body=(
       !,
        bcUnaryAllDiff:split2diffs(Ints,ConstrsH-ConstrsT)
   ),
   bParser:addConstraint(Head,Body).

split2diffs([],Constrs-Constrs):-!.
split2diffs([_],Constrs-Constrs):-!.
split2diffs([A|As],ConstrsH-ConstrsT):-!,
   bcInteger:getUnaryNumber(A,Au),
   split2diffs(As,Au,ConstrsH-ConstrsM),
   split2diffs(As,ConstrsM-ConstrsT).

split2diffs([],_,Constrs-Constrs):-!.
split2diffs([B|As],Au,ConstrsH-ConstrsT):-
    bcInteger:getUnaryNumber(B,Bu),
    bcUnaryDiff:unaryDiffType(Type),
    bcUnaryDiff:unaryDiffSimplify(bc(Type,[Au,Bu]),Constr, 1),
    (Constr==none ->
        split2diffs(As,Au,ConstrsH-ConstrsT)
    ;
        ConstrsH=[Constr|ConstrsM],
        split2diffs(As,Au,ConstrsM-ConstrsT)
    ).
:- else.
:- bSettings:allDiffDecompose(X), writef('ERROR: "%w" is wrong value for bSettings:allDiffDecompose !\n',[X]),flush_output,halt.
:- endif.

%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
unaryAllDiffType([
            bcUnaryAllDiff:unaryAllDiffSimplify,
            bcUnaryAllDiff:unaryAllDiffSimplifyAdv,
            bcUnaryAllDiff:unaryAllDiffDecompose,
            0,
            unaryAllDiff
           ]).

unaryPermutationType([
            bcUnaryAllDiff:unaryPermutationSimplify,
            bcUnaryAllDiff:unaryPermutationSimplifyAdv,
            bcUnaryAllDiff:unaryPermutationDecompose,
            0,
            unaryPermutation
           ]).

%%% ------------------------- %%%
%%%  Create Data Structures   %%%
%%% ------------------------- %%%

createDataStructs(Ints,Buckets,Numbers):-
    fixIntegers(Ints,FInts),
    msort(FInts,SFInts),
    addNumbers2DataStructs(SFInts,1,Buckets,Numbers).

fixIntegers([Int|Ints],[(Min,Drct,Unry)|FInts]):-!,
    bcInteger:getUnaryNumber(Int,(Min,Max,Unry,_)),!,
    bcInteger:getDirectNumber(Int,(Min,Max,Drct,_)),!,
    fixIntegers(Ints,FInts).
fixIntegers([],[]):-!.

addNumbers2DataStructs([(Min,Direct,Unary)|Ints],I,Buckets,[(I,Min,Direct)|Numbers]):-
    addNumber2Buckets(Direct,[1|Unary],Min,I,Buckets),
    I1 is I + 1,
    addNumbers2DataStructs(Ints,I1,Buckets,Numbers).
addNumbers2DataStructs([],_,Buckets,[]):-!,
    closeBuckets(Buckets).

closeBuckets([]):-!.
closeBuckets([B|Bs]):-!,
    closeList(B),
    closeBuckets(Bs).

closeList([]):-!.
closeList([_|Bs]):-!,
    closeList(Bs).

addNumber2Buckets([D0|Drcts],[U0,U1|Unrys],Val,NumID,Buckets):-
    lit2plit(D0,Xl,Xop),
    addVal2Buckets(Val,Buckets,(Xl,Xop,NumID,U0,U1),RBuckets),
    Val1 is Val + 1,
    addNumber2Buckets(Drcts,[U1|Unrys],Val1,NumID,RBuckets).
addNumber2Buckets([D0],[U0],Val,NumID,Buckets):-
    lit2plit(D0,Xl,Xop),
    addVal2Buckets(Val,Buckets,(Xl,Xop,NumID,U0,-1),_).

%addVal2Buckets(Val,Buckets,NumVal,RBuckets):-
%    var(Buckets),!,
%    Buckets=[[Val,NumVal|_]|RBuckets].
addVal2Buckets(Val,[[Val|BVals]|RBuckets],NumVal,RBuckets):-!,
    addToEndOfList(BVals,NumVal).
%addVal2Buckets(Val,[[BVal|_]|Buckets],NumVal,RBuckets):-!,
%    BVal<Val,!,
addVal2Buckets(Val,[_|Buckets],NumVal,RBuckets):-!,
    addVal2Buckets(Val,Buckets,NumVal,RBuckets).

addToEndOfList(List,Val):-var(List),!, List=[Val|_].
addToEndOfList([_|List],Val):-!,addToEndOfList(List,Val).


% --------------------------------
% | Simplify                     |
% --------------------------------
unaryAllDiffSimplify(bc(Type,[Buckets,Numbers,Cnts]),Constr,Changed):-!,
    reduceBucketsDiff(Buckets,Numbers,Cnts,NBuckets,NNumbers,NCnts,Changed),!,
    (Changed==1 ->
        NCnts=(NBCnt,NNCnt),
        %length(NBuckets,NBCnt2),
        %length(NNumbers,NNCnt2),
        %((NBCnt2\==NBCnt ; NNCnt2\==NNCnt) -> throw(bug(simplify,allDiff_wrong_bucket_cnt) ; true),
        (NBCnt<NNCnt -> throw(unsat) ;
        (NNCnt < 2 ->
           Constr=none
        ;
        (NBCnt==NNCnt ->
           unaryPermutationType(PType),
           unaryPermutationSimplify(bc(PType,[NBuckets,NNumbers]),Constr,_)
        ;
           unaryAllDiffSimplify(bc(Type,[NBuckets,NNumbers,NCnts]),Constr,_)
        )
        ))
    ;
        Constr=bc(Type,[NBuckets,NNumbers,NCnts])
    ).

unaryAllDiffSimplifyAdv(bc(Type,[Buckets,Numbers,Cnts]),Constr,Changed):-!,
    removeHallSet2(Buckets,Numbers,NBuckets,NNumbers,Changed),!,
    (Changed==1 ->
        ((NNumbers=[] ; NNumbers=[_])  ->
            Constr=none
        ;
            length(NBuckets,BCnt),
            length(NNumbers,NCnt),
            patternsInBuckets(NBuckets,_),
            Constr=bc(Type,[NBuckets,NNumbers,(BCnt,NCnt)])
        )
    ;
        patternsInBuckets(Buckets,Changed),
        Constr=bc(Type,[Buckets,Numbers,Cnts])
    ).

%unaryPermutationSimplify(X,X,_):-!.
unaryPermutationSimplify(bc(Type,[Buckets,Numbers]),Constr,Changed):-!,
    reduceBucketsPerm(Buckets,Numbers,NBuckets,NNumbers,Changed),!,
    (Changed==1 ->
        (NNumbers=[] ->
           Constr=none
        ;
           unaryPermutationSimplify(bc(Type,[NBuckets,NNumbers]),Constr,_)
        )
    ;
        Constr=bc(Type,[NBuckets,NNumbers])
    ).

unaryPermutationSimplifyAdv(bc(Type,[Buckets,Numbers]),Constr,Changed):-!,
    removeDoubleBuckets(Buckets,Numbers,TBuckets,TNumbers,Changed),!,
    removeHallSet2(TBuckets,TNumbers,NBuckets,NNumbers,Changed),!,
    (NNumbers=[] ->
        Changed=1,
        Constr=none
    ;
        patternsInBuckets(NBuckets,Changed),
        Constr=bc(Type,[NBuckets,NNumbers])
    ).

%%% ------------------------- %%%
%%%  reduce buckets           %%%
%%% ------------------------- %%%
reduceBucketsDiff([[Bid|B]|Bs],Nums,Cnts,NBs,NNums,NCnts,Changed):-
    reduceBucket(B,NB,FoundOne,Changed),
    (NB=[] ->
       Cnts=(BCnt,NCnt),
       BCnt1 is BCnt - 1,
       Changed=1,
       (var(FoundOne) ->
           reduceBucketsDiff(Bs,Nums,(BCnt1,NCnt),NBs,NNums,NCnts,Changed)
       ;
           FoundOne=one((Nid,U0,U1)),
           litAsgnTrue(U0), litAsgnFalse(U1),
           removeNumberFromDS(Nid,Nums,NumsT),
           NCnt1 is NCnt - 1,
           reduceBucketsDiff(Bs,NumsT,(BCnt1,NCnt1),NBs,NNums,NCnts,Changed)
       )
    ;
       NBs=[[Bid|NB]|MBs],
       reduceBucketsDiff(Bs,Nums,Cnts,MBs,NNums,NCnts,Changed)
    ).
reduceBucketsDiff([],Nums,Cnts,[],Nums,Cnts,_):-!.


reduceBucketsPerm([[Bid|B]|Bs],Nums,NBs,NNums,Changed):-!,
    reduceBucket(B,NB,FoundOne,Changed),!,
    (NB=[] ->
       (var(FoundOne) ->
           throw(unsat)
       ;
           Changed=1,
           FoundOne=one((Nid,U0,U1)),
           litAsgnTrue(U0), litAsgnFalse(U1),
           removeNumberFromDS(Nid,Nums,NumsT),
           reduceBucketsPerm(Bs,NumsT,NBs,NNums,_)
       ) ;
    (NB=[(X1,X1op,Nid,U0,U1)] ->
       Changed=1,
       plitAsgnTrue((X1,X1op)),
       litAsgnTrue(U0), litAsgnFalse(U1),
       removeNumberFromDS(Nid,Nums,NumsT),
       reduceBucketsPerm(Bs,NumsT,NBs,NNums,_) ;
    (NB=[(X1,X1op,_),(X2,X2op,_)] ->
       ((X1==X2, -X1op=:=X2op ,!) ; Changed=1, plitUnifyDiff((X1,X1op),(X2,X2op))),!,
       NBs=[[Bid|NB]|MBs],
       reduceBucketsPerm(Bs,Nums,MBs,NNums,Changed) ;
    NBs=[[Bid|NB]|MBs],
    reduceBucketsPerm(Bs,Nums,MBs,NNums,Changed)
    ))
    ).
reduceBucketsPerm([],Nums,[],Nums,_):-!.

removeNumberFromDS(Nid,[(Nid,_,Drct)|Nums],Nums):-!,
    asgnFalsesInDirect(Drct).
removeNumberFromDS(Nid,[Num|Nums],[Num|NNums]):-!,
    removeNumberFromDS(Nid,Nums,NNums).
%removeNumberFromDS(_,[],_):-!,
    %throw(bug(simplify,allDiff_removeNum)).
    
asgnFalsesInDirect([X|Xs]):-
    ground(X),!,
    (X =:= -1 ->
       asgnFalsesInDirect(Xs)
    ;
       litAsgnFalses(Xs)
    ).
asgnFalsesInDirect([X|Xs]):-!,
    litAsgnFalse(X),!,
    asgnFalsesInDirect(Xs).

%%% ------------------------- %%%
%%%  reduce bucket size       %%%
%%% ------------------------- %%%
reduceBucket(Pbits,NewPbits,FoundOne,Changed):-!,
    reduceBucket(Pbits,TPbits,FoundOne,Changed,NeedSort),
    (var(FoundOne) ->
        (NeedSort==1 ->
            msort(TPbits,TPbits2),
            reduceBucket(TPbits2,NewPbits,FoundOne,Changed)
        ;
            NewPbits=TPbits
        ) ;
    (FoundOne=one(_) ->
         (TPbits=[] ; tagLitAsgnFalses(TPbits), Changed=1),!,
         NewPbits=[] ;
    FoundOne=two(X,Y),
         (TPbits=[] ; tagLitAsgnFalses(TPbits), Changed=1),!,
         NewPbits=[X,Y]
    )).

reduceBucket([(X1,Xop1,Info)|PWbits],NewPWbits,FoundOne,Changed,NeedSort):-!,
    (ground(X1) ->
        Changed=1,
        (X1*Xop1 =:= 1 ->
            FoundOne=one(Info),
            NewPWbits=PWbits
        ;
            Info=(_,X1u1,X1u2),
            litUnify(X1u1,X1u2),
            reduceBucket(PWbits,NewPWbits,FoundOne,1,NeedSort)
        ) ;
    (var(X1) ->
        reduceBucket(PWbits,(X1,Xop1,Info),NewPWbits,FoundOne,Changed,NeedSort) ;
    lit2plit(X1,X1n,X1op),
    Xop1n is Xop1 * X1op,
    reduceBucket(PWbits,(X1n,Xop1n,Info),NewPWbits,FoundOne,Changed,NeedSort)
    )).
reduceBucket([],[],_,_,_):-!.

reduceBucket([(X2,X2op,Info2)|PWbits],(X1,X1op,Info1),NewPWbits,FoundOne,Changed,NeedSort):-!,
    (ground(X2) ->
        Changed=1,
        (X2*X2op =:= 1 ->
            FoundOne=one(Info2),
            NewPWbits=[(X1,X1op,Info1)|PWbits]
        ;
            Info2=(_,X2u1,X2u2),
            litUnify(X2u1,X2u2),
            reduceBucket(PWbits,(X1,X1op,Info1),NewPWbits,FoundOne,1,NeedSort)
        ) ;
    (var(X2) ->
        (X2 == X1 ->
             (X2op==X1op ->
                  Changed=1,
                  plitAsgnFalse((X2,X2op)),
                  Info2=(_,X2u1,X2u2),
                  litUnify(X2u1,X2u2),
                  Info1=(_,X1u1,X1u2),
                  litUnify(X1u1,X1u2),
                  reduceBucket(PWbits,NewPWbits,FoundOne,1,NeedSort)
             ;
                  FoundOne=two((X1,X1op,Info1),(X2,X2op,Info2)),
                  NewPWbits=PWbits
             ) ;
        (X2 @> X1 ->
            NewPWbits=[(X1,X1op,Info1)|MorePWbits],
            reduceBucket(PWbits,(X2,X2op,Info2),MorePWbits,FoundOne,Changed,NeedSort)
        ;
            NeedSort=1,
            NewPWbits=[(X2,X2op,Info2)|MorePWbits],
            reduceBucket(PWbits,(X1,X1op,Info1),MorePWbits,FoundOne,Changed,NeedSort)
        ))
    ;
        lit2plit(X2,X2n,X2opb),
        X2opn is X2op*X2opb,
        reduceBucket([(X2n,X2opn,Info2)|PWbits],(X1,X1op,Info1),NewPWbits,FoundOne,Changed,NeedSort)
    )).

reduceBucket([],PWx,[PWx],_,_,_):-!.


tagLitAsgnFalses([(Xl,Xop,_,U1,U2)|Xs]):-!,
%tagLitAsgnFalses([(Xl,Xop,_)|Xs]):-!,
   plitAsgnFalse((Xl,Xop)),
   litUnify(U1,U2),
   tagLitAsgnFalses(Xs).
tagLitAsgnFalses([]):-!.

%%% ------------------------------------------- %%%
%%% permutation and double buckets optimization %%%
%%% ------------------------------------------- %%%

removeDoubleBuckets(Buckets,Numbers,NBuckets,NNumbers,Changed):-
    findDoubleBuckets(Buckets,DoubleBuckets),
    (DoubleBuckets=[] ->
       NBuckets=Buckets,
       NNumbers=Numbers
    ;
       Changed=1,
       removeDblNumbers(DoubleBuckets,Numbers,NNumbers),
       removeDblBuckets(DoubleBuckets,Buckets,NBuckets)
    ).

findDoubleBuckets(Buckets,DoubleBuckets):-!,
    getDoubleBuckets(Buckets,DBuckets),
    ((DBuckets=[] ; DBuckets=[_]) ->
         DoubleBuckets=[]
    ;
         sort(DBuckets,SDBuckets),
         findPairs(SDBuckets,DoubleBuckets)
    ).

getDoubleBuckets([[Bid,N1,N2]|Buckets],[(NidS,NidL,Bid)|DblBuckets]):-!,
    N1=(_,_,N1id,_),
    N2=(_,_,N2id,_),
    (N1id>N2id ->
       NidS=N2id,
       NidL=N1id
    ;
       NidS=N1id,
       NidL=N2id
    ),
    getDoubleBuckets(Buckets,DblBuckets).
getDoubleBuckets([_|Buckets],DblBuckets):-!,
    getDoubleBuckets(Buckets,DblBuckets).
getDoubleBuckets([],[]):-!.

removeDblBuckets(DoubleBuckets,Buckets,NBuckets):-!,
    getDblBucketIds(DoubleBuckets,Ids),
    sort(Ids,BIds),
    removeBucketsByID(BIds,Buckets,NBuckets).

getDblBucketIds([(_,_,Bid1,Bid2)|DBs],[Bid1,Bid2|BIds]):-!,
    getDblBucketIds(DBs,BIds).
getDblBucketIds([],[]):-!.

removeBucketsByID([],Buckets,Buckets):-!.
removeBucketsByID([Bid|BIds],[[Bid|_]|Buckets],NBuckets):-!,
    removeBucketsByID(BIds,Buckets,NBuckets).
removeBucketsByID(BIds,[Bucket|Buckets],[Bucket|NBuckets]):-!,
    removeBucketsByID(BIds,Buckets,NBuckets).

removeDblNumbers([(Nid1,Nid2,Val1,Val2)|DBs],Numbers,NNumbers):-!,
    ((select((Nid1,Min1,DrctBits1),Numbers,Numbers1),!,
      select((Nid2,Min2,DrctBits2),Numbers1,Numbers2)) ->
        setTwoValuesDirect(Min1,Val1,Val2,DrctBits1),
        setTwoValuesDirect(Min2,Val1,Val2,DrctBits2)
    ;
        throw(unsat)
    ),!,
    removeDblNumbers(DBs,Numbers2,NNumbers).
removeDblNumbers([],Numbers,Numbers):-!.

setTwoValuesDirect(Min,Min,Val2,[X|Bits]):-!,
    Min1 is Min + 1,
    setTwoValuesDirect_s2(Min1,Val2,X,Bits).
setTwoValuesDirect(Min,Val1,Val2,[X|Bits]):-!,
    litAsgnFalse(X),
    Min1 is Min + 1,
    setTwoValuesDirect(Min1,Val1,Val2,Bits).

setTwoValuesDirect_s2(Min,Min,X,[Y|Bits]):-!,
    litUnify(X,-Y),
    litAsgnFalses(Bits).
setTwoValuesDirect_s2(Min,Val2,X,[Y|Bits]):-!,
    litAsgnFalse(Y),
    Min1 is Min + 1,
    setTwoValuesDirect_s2(Min1,Val2,X,Bits).

%%% ----------------------- %%%
%%%  removes Hall-Set of 2  %%%
%%% ----------------------- %%%
removeHallSet2(Buckets,Numbers,NBuckets,NNumbers,Changed):-!,
    findHallSet2(Numbers,HallSets2),!,
    (HallSets2=[] ->
         NBuckets=Buckets,
         NNumbers=Numbers
    ;
         Changed=1,
         removeHallSet2_numbers(HallSets2,Numbers,NNumbers),
         removeHallSet2_buckets(HallSets2,Buckets,NBuckets)
    ).

findHallSet2(Numbers,HallSets2):-
    findNumWdom2(Numbers,Dom2Numbers),
    ((Dom2Numbers=[] ; Dom2Numbers=[_]) ->
         HallSets2=[]
    ;
         sort(Dom2Numbers,SDom2Numbers),
         findPairs(SDom2Numbers,HallSets2)
    ).

findNumWdom2([(NId,Min,DrctBits)|Numbers],Dom2Numbers):-!,
    getNumberDomSize(DrctBits,Min,Val1,Val2,DomSize),
    (DomSize \== 2 ->
        findNumWdom2(Numbers,Dom2Numbers)
    ;
        Dom2Numbers=[(Val1,Val2,NId)|MDom2Numbers],
        findNumWdom2(Numbers,MDom2Numbers)
    ).
findNumWdom2([],[]):-!.

removeHallSet2_numbers([(_,_,NId1,NId2)|HallSets2],Numbers,NNumbers):-!,
    ((select((NId1,_),Numbers ,Numbers1),!,
      select((NId2,_),Numbers1,Numbers2)) ->
          removeHallSet2_numbers(HallSets2,Numbers2,NNumbers)
      ;
          throw(unsat)
      ).
removeHallSet2_numbers([],Numbers,Numbers):-!.


removeHallSet2_buckets([(Val1,Val2,NId1,NId2)|HallSets2],Buckets,NBuckets):-!,
      ((select([Val1|Bucket1],Buckets ,Buckets1),
        select([Val2|Bucket2],Buckets1,Buckets2)) ->
          fixHallSet2Bucket(Bucket1,NId1,NId2),
          fixHallSet2Bucket(Bucket2,NId1,NId2),
          removeHallSet2_buckets(HallSets2,Buckets2,NBuckets)
      ;
          throw(unsat)
      ).
removeHallSet2_buckets([],Buckets,Buckets):-!.


fixHallSet2Bucket([(Xl,Xop,Nid,A,B)|Bucket],NId1,NId2):-!,
      (Nid==NId1 ->
          fixHallSet2Bucketv2(Bucket,NId2,(Xl,Xop)) ;
      (Nid==NId2 ->
          fixHallSet2Bucketv2(Bucket,NId1,(Xl,Xop)) ;
      plitAsgnFalse((Xl,Xop)),
      litUnify(A,B),
      fixHallSet2Bucket(Bucket,NId1,NId2)
      )).
fixHallSet2Bucket([],_,_):-!,
     throw(unsat).

fixHallSet2Bucketv2([(Xl,Xop,Nid,A,B)|Bucket],NId2,Px):-!,
     (Nid==NId2 ->
         plitUnifyDiff((Xl,Xop),Px),
         tagLitAsgnFalses(Bucket)
     ;
         plitAsgnFalse((Xl,Xop)),
         litUnify(A,B),
         fixHallSet2Bucketv2(Bucket,NId2,Px)
     ).
fixHallSet2Bucketv2([],_,_):-!,
     throw(unsat).

getNumberDomSize([D|Drct],Min,Val1,Val2,DomSize):-!,
    (ground(D) ->
        (D=:= -1 ->
            Min1 is Min + 1,
            getNumberDomSize(Drct,Min1,Val1,Val2,DomSize)
        ;
            DomSize=1,
            litAsgnFalses(Drct)
        )
    ;
        Val1=Min,
        Min1 is Min + 1,
        getNumberDomSize(Drct,Min1,Val2,DomSize)
    ).
getNumberDomSize([],_,_,_,_):-!,
    throw(unsat).

getNumberDomSize([D|Drct],Min,Val2,DomSize):-!,
    (ground(D) ->
        (D=:= -1 ->
            Min1 is Min + 1,
            getNumberDomSize(Drct,Min1,Val2,DomSize)
        ;
            DomSize=1,
            litAsgnFalses(Drct)
        )
    ;
        Val2=Min,
        (allAreFalses(Drct),!, DomSize=2 ; DomSize=3)
    ).
getNumberDomSize([],_,_,1):-!.


allAreFalses([X|Xs]):-!,
    ground(X), X=:= -1,
    allAreFalses(Xs).
allAreFalses([]):-!.

% ---- AUX  --- %

findPairs([A|As],Pairs):-!,
    findPairs(As,A,Pairs).
findPairs([(V1,V2,I2)|As],(V1,V2,I1),[(V1,V2,IS,IL)|Pairs]):-!,
    (I1>I2 ->
        IS=I2,
        IL=I1
    ;
        IS=I1,
        IL=I2
    ),
    findPairs(As,(V1,V2,I2),Pairs).
findPairs([A2|As],_A1,Pairs):-!,
    findPairs(As,A2,Pairs).
findPairs([],_,[]):-!.

%%% ------------------------- %%%
%%%  patterns in buckets      %%%
%%% ------------------------- %%%
patternsInBuckets([[_|Bucket]|Buckets],Changed):-!,
   patternsInBucket(Bucket,Changed),
   patternsInBuckets(Buckets,Changed).
patternsInBuckets([],_):-!.

patternsInBucket([_],_):-!.
patternsInBucket([(_,_,_,U1,U2)|Bucket],Changed):-!,
   lit2plit(U1,U1l,U1op),
   lit2plit(U2,U2l,U2op),
   (U1l==U2l ->
      (U1op==U2op,! ; litAsgnTrue(U1))
   ;
      patternsInBucket(Bucket,U1l,U1op,U2l,U2op,Changed)
   ),
   patternsInBucket(Bucket,Changed).

patternsInBucket([(_,_,_,V1,V2)|Bucket],U1l,U1op,U2l,U2op,Changed):-!,
   lit2plit(V1,V1l,V1op),
   lit2plit(V2,V2l,V2op),
   (V1l==V2l ->
       patternsInBucket(Bucket,U1l,U1op,U2l,U2op,Changed) ;
   ((U1l==V2l, U2l==V1l) ->
      (((U1op\==V2op, U2op\==V1op) ; (U1op==V2op, U2op==V1op)) ->
          % (1) [A,B],[-B,-A] -> [A,A],[-A,-A]
          % (2) [A,B],[B,A] -> [A,A],[A,A]
           Changed=1,
           plitUnify((U1l,U1op),(U2l,U2op)) ;
      (U1op==V2op ->
          % (3) [A,B],[-B,A] -> [A,0],[1,A]
          ((ground(U2l), U2l*U2op =:= -1) ;
           (Changed=1 , plitAsgnFalse((U2l,U2op)))),!,
          patternsInBucket(Bucket,U1l,U1op,1,-1,Changed)
      ;
          % (4) [A,B],[B,-A] -> [1,B],[B,0]
          ((ground(U1l), U1l*U1op =:= 1) ;
           (Changed=1 , plitAsgnTrue((U1l,U1op)))),!,
          patternsInBucket(Bucket,1,1,U2l,U2op,Changed)
      ))
   ;
      patternsInBucket(Bucket,U1l,U1op,U2l,U2op,Changed)
   )).
patternsInBucket([],_,_,_,_,_):-!.

% --------------------------------
% | Decompose                    |
% --------------------------------
unaryAllDiffDecompose(bc(_,[Buckets|_]),Constrs):-
   bcAtMostOne:amoType(AMOType),
   buckets2SumBits(Buckets,AMOType,Constrs).

unaryPermutationDecompose(bc(_,[Buckets|_]),Constrs):-
   bcExactlyOne:exoType(EXOType),
   buckets2SumBits(Buckets,EXOType,Constrs).

buckets2SumBits([[_,_]|Buckets],SUMType,Constrs):-!,
   buckets2SumBits(Buckets,SUMType,Constrs).
buckets2SumBits([[_|Bucket]|Buckets],SUMType,[bc(SUMType,Vec)|Constrs]):-!,
   bucket2PLits(Bucket,Vec),
   buckets2SumBits(Buckets,SUMType,Constrs).
buckets2SumBits([],_,[]):-!.

bucket2PLits([(Xl,Xop,_)|Bucket],[(Xl,Xop)|Vec]):-!,
   bucket2PLits(Bucket,Vec).
bucket2PLits([],[]):-!.