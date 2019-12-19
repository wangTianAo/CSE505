% Author: Amit Metodi
% Last Updated: 10/04/2012

:- module(weightUnaries, [ ]).
:- use_module('auxLiterals').
%:- use_module('auxUnarynum').
%:- use_module('auxLists').


wunariesFix2PosWghtInt([U|Us],[(1,NMax,Bits,LBit)|WUs],CurEqTo,EqTo):-!,
   bcInteger:getUnaryNumber(U,(Min,Max,Bits,LBit)),
   NMax is Max - Min,
   UpdEqTo is CurEqTo - Min,
   wunariesFix2PosWghtInt(Us,WUs,UpdEqTo,EqTo).
wunariesFix2PosWghtInt([],[],EqTo,EqTo):-!.


wunariesFix2PosWghtInt([0|As],[_|Us],WUs,CurEqTo,EqTo):-!,
   wunariesFix2PosWghtInt(As,Us,WUs,CurEqTo,EqTo).
wunariesFix2PosWghtInt([A|As],[U|Us],[(W,NMax,Bits,LBit)|WUs],CurEqTo,EqTo):-!,
   (A > 0 ->
       W is A,
       bcInteger:getUnaryNumber(U,(Min,Max,Bits,LBit))
   ;
       W is -A,
       bcInteger:getUnaryNumber(-U,(Min,Max,Bits,LBit))
   ),
   NMax is Max - Min,
   UpdEqTo is CurEqTo - W*Min,
   wunariesFix2PosWghtInt(As,Us,WUs,UpdEqTo,EqTo).
wunariesFix2PosWghtInt([],[],[],EqTo,EqTo):-!.

   

%% get the max cost
wunariesMax([(W,M,_)|Us],CurMax,Max):-!,
   CurMax1 is CurMax + M*W,
   wunariesMax(Us,CurMax1,Max).
wunariesMax([],Max,Max):-!.


wunariesEqTo([(W,M,Bits,_)|Us],Max,EqTo,Changed):-!,
   (M*W =< EqTo -> true ; !,
       Changed=1,
       NMax is EqTo // W,
       auxLists:listDropFrom(NMax,Bits,FalseBits),!,
       litAsgnFalses(FalseBits)
   ),!,
   AtLeast is (EqTo - (Max - M*W) + W-1) // W,
   (AtLeast =< 0 -> true ; !,
       Changed=1,
       auxLists:listKeepFrom(AtLeast,Bits,TrueBits),!,
       litAsgnTrues(TrueBits)
   ),!,
   wunariesEqTo(Us,Max,EqTo,Changed).
wunariesEqTo([],_,_,_):-!.





wunairesUpdate([(W,M,Bits,LBit)|Us],OnesSoFar,NWInts,OnesFound,Changed):-!,
   ((ground(LBit) ; (Bits=[B0|_], ground(B0))) ->
       Changed=1,
       auxUnarynum:unarynumFix((0,M,Bits,LBit),(TMin,TMax,NBits,NLBit)),
       OnesSoFar1 is OnesSoFar + W*TMin,
       NMax is TMax - TMin,
       (NMax > 0 ->
           NWInts=[(W,NMax,NBits,NLBit)|MWInts],
           wunairesUpdate(Us,OnesSoFar1,MWInts,OnesFound,_)
       ;
           wunairesUpdate(Us,OnesSoFar1,NWInts,OnesFound,_)
       ) ;
   NWInts=[(W,M,Bits,LBit)|MWInts],
   wunairesUpdate(Us,OnesSoFar,MWInts,OnesFound,Changed)
   ).
wunairesUpdate([],OnesFound,[],OnesFound,_):-!.





wunariesAsgnMaxs([(_,_,Bits,_)|Us]):-!,
   litAsgnTrues(Bits),
   wunariesAsgnMaxs(Us).
wunariesAsgnMaxs([]):-!.

wunariesAsgnZeros([(_,_,Bits,_)|Us]):-!,
   litAsgnFalses(Bits),
   wunariesAsgnZeros(Us).
wunariesAsgnZeros([]):-!.