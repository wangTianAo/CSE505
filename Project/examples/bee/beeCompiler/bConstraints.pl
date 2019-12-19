:- module(bConstraints, []).
%%% AUX modules
:- ['auxs/auxLists'].
:- ['auxs/auxLiterals'].
:- ['auxs/atLeastOne'].
:- ['auxs/atMostOne'].
:- ['auxs/xorVec'].
:- ['auxs/auxUnarynum'].
:- ['auxs/weightBits'].
:- ['auxs/weightUnaries'].

%%% Basic Boolean Constraints
:- ['constraints/bcBool'].
:- ['constraints/bcAtLeastOne'].
:- ['constraints/bcAtMostOne'].
:- ['constraints/bcExactlyOne'].      %% requires: bcAtLeastOne, bcAtMostOne
:- ['constraints/bcOr'].              %% requires: bcAtLeastOne
:- ['constraints/bcXor'].
:- ['constraints/bcITE'].             %% requires: bcXor, bcAtLeastOne
:- ['constraints/bcBoolEq'].          %% requires: bcOr, bcXor, bcAtLeastOne

%%% Basic Integer Constraitns
:- ['constraints/bcSorted'].
:- ['constraints/bcUnaryDirectChnl']. %% requires: bcSorted, bcExactlyOne
:- ['constraints/bcInteger'].         %% requires: bcSorted, bcUnaryDirectChnl
:- ['constraints/bcChannel'].         %% requires: bcInteger
:- ['constraints/bcIntegerK'].        %% requires: bcInteger

%%% Boolean element
:- ['constraints/bcBoolElement'].     %% requires: bcInteger, bcITE

%%% Arithmetic Constraints
:- ['constraints/bcComparator'].
:- ['constraints/bcUnaryAdder'].      %% requires: bcInteger, bcComparator
:- ['constraints/bcUnaryAdderAgeB'].  %% requires: bcInteger, bcComparator, bcUnaryAdder
:- ['constraints/bcSumUnaries'].      %% requires: bcInteger, bcUnaryAdder, bcSumBits
:- ['constraints/bcSumUnariesLEqK'].  %% requires: bcInteger, bcUnaryAdder, bcSumBits, bcSumBitsLEqK, bcSumUnaries
:- ['constraints/bcSumCondUnaries'].  %% requires: bcInteger, bcSumUnaries, bcSumUnariesLEqK
:- ['constraints/bcSumBits'].         %% requires: bcInteger, bcExactlyOne, bcComparator, bcUnaryAdder, bcUnaryAdderAgeB, bcSumUnaries
:- ['constraints/bcSumBitsLEqK'].     %% requires: bcInteger, bcSumBits, bcAtLeastOne, bcAtMostOne

:- ['constraints/bcUnaryMax'].        %% requires: bcInteger, bcAtLeastOne, bcOr
:- ['constraints/bcUnaryAbs'].        %% requires: bcInteger, bcUnaryMax
:- ['constraints/bcUnaryTimes'].      %% requires: bcInteger, bcAtLeastOne, bcUnaryDiffReif, bcUnaryAbs, bcUnaryMax
:- ['constraints/bcUnaryDiv'].        %% requires: bcInteger, bcAtLeastOne, bcUnaryAbs, bcUnaryMax
:- ['constraints/bcUnaryMod'].        %% requires: bcInteger, bcAtLeastOne, bcXor, bcUnaryAbs, bcUnaryMax, bcUnaryTimes, bcUnaryMod, bcUnaryAdder
:- ['constraints/bcUnaryTimesAry'].   %% requires: bcInteger, bcUnaryTimes

%%% Integer Relation Constraitns
:- ['constraints/bcUnaryLEq'].        %% requires: bcInteger
:- ['constraints/bcUnaryLEqReif'].    %% requires: bcInteger, bcUnaryLEq, bcOr
:- ['constraints/bcUnaryBetween'].    %% requires: bcInteger
:- ['constraints/bcUnaryDiff'].       %% requires: bcInteger, bcAtLeastOne
:- ['constraints/bcUnaryDiffReif'].   %% requires: bcInteger, bcUnaryDiff, bcXor
:- ['constraints/bcDirectRels'].      %% requires: bcInteger, bcOr
:- ['constraints/bcUnaryAllDiff'].    %% requires: bcInteger, bcUnaryDiff, bcAtMostOne, bcExactlyOne
:- ['constraints/bcUnaryAllDiffCond'].%% requires: bcUnaryDiffReif, bcOr
:- ['constraints/bcUnaryAllDiffReif'].%% requires: bcInteger, bcDirectRels, bcUnaryAllDiff, bcOr

%%% Boolean Arrays Lexiacal Order
:- ['constraints/bcVectorLex'].       %% requires: bcAtLeastOne
:- ['constraints/bcVectorLexReif'].   %% requires: bcVectorLex, bcOr

%%% Integer Arrays Lexiacal Order
:- ['constraints/bcUnaryLex'].        %% requires: bcInteger, bcUnaryLEq, bcOr, bcAtLeastOne

%%% Integer Array Eq/Neq/Eq Reif/Neq Reif
:- ['constraints/bcUnaryArrayEq'].    %% requires: bcInteger, bcOr, bcUnaryDiffReif

%%% Boolean Arrays Different
:- ['constraints/bcVectorDiffReif'].  %% requires: bcAtLeastOne, bcOr, bcXor

%%% Sum Mod K
:- ['constraints/bcSumModK'].         %% requires: bcInteger, bcSumBits, bcUnaryAdder, bcUnaryMod, bcITE
:- ['constraints/bcSumDivModK'].      %% requires: bcInteger, bcSumBits, bcUnaryAdder, bcUnaryDiv, bcUnaryMod, bcITE, bcBoolElement
