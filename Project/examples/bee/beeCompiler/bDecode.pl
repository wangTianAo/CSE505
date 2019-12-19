% Author: Amit Metodi
% Last Updated: 18/06/2013

:- module(bDecode, [decodeInt/2, decodeIntArray/2, decodeIntMatrix/2, isFullyAssginedInt/1]).

decodeIntMatrix([IntRow|Ints],[ValRow|Vals]):-!,
    decodeIntArray(IntRow,ValRow),!,
    decodeIntMatrix(Ints,Vals).
decodeIntMatrix([],[]):-!.

decodeIntArray([Int|Ints],[Val|Vals]):-!,
    decodeInt(Int,Val),!,
    decodeIntArray(Ints,Vals).
decodeIntArray([],[]):-!.

decodeInt(Int,_):-var(Int),!,fail.
decodeInt((int,Min,Max,Reps),Val):-!,
    decodeInt_aux(Reps,Min,Max,Val).
decodeInt(Int,Int):-
    integer(Int),!.
decodeInt(-(Int),Val):-!,
    decodeInt(Int,NVal),
    Val is -NVal.

decodeInt_aux(Reps,Min,Max,Val):-!,
    (\+ var(Reps) ->
        Reps=[(RType,RData)|MReps],
        (decodeInt_rep(RType,Min,Max,RData,Val) ->
            true
        ;
            decodeInt_aux(MReps,Min,Max,Val)
        )
    ;
        throw(decodeInt_err('Failed to decode an int varaible !'))
    ).


isFullyAssginedInt(X):-var(X),!,fail.
isFullyAssginedInt(X):-integer(X),!.
isFullyAssginedInt(-(X)):-!,isFullyAssginedInt(X).
isFullyAssginedInt((int,_,_,Reps)):-!,
    isFullyAssginedInt_aux(Reps).

isFullyAssginedInt_aux(Reps):-!,
    \+ var(Reps),!,
    Reps=[(_RType,RData)|MReps],
    (ground(RData) -> true ;
    !,isFullyAssginedInt_aux(MReps)).


%% -----------------------------------------
%% Specific decode representation predicates
decodeUnary([B|Bs],Indx,Val):-!,
    (ground(B) ; auxLiterals:litAsgnFalse(B)),!,
    (B =:= 1 ->
        Indx1 is Indx + 1,
        decodeUnary(Bs,Indx1,Val)
    ;
        Val=Indx
    ).
decodeUnary([],Val,Val):-!.


decodeDirect([B|Bs],Indx,Val):-!,
    (ground(B) ; auxLiterals:litAsgnFalse(B)),!,
    (B =:= 1 ->
        Val=Indx
    ;
        Indx1 is Indx + 1,
        decodeDirect(Bs,Indx1,Val)
    ).




:-dynamic(decodeInt_rep(_,_,_,_,_)).

decodeInt_rep(order,Min,_Max,Data,Val):-!,
    Data=(Bits,_),
    decodeUnary(Bits,Min,Val).

decodeInt_rep(direct,Min,_Max,Data,Val):-!,
    Data=(Bits,_),
    decodeDirect(Bits,Min,Val).
