% Verify DNA words solution
% Author: Amit Metodi
% Date: 11/12/2010

:- module(dnaVerify, [
                    verifyDNAWords/1
                    ]).

verifyDNAWords([Word|Words]):-
   (isGoodWord(Word) -> true ; writeln(badWord(Word)),!,fail),
   verifyDiffWords(Words,Word),
   verifyDNAWords(Words).
verifyDNAWords([]).


verifyDiffWords([Word2|Words],Word1):-!,
   countDiffs(Word1,Word2,Diffs),!,
   (Diffs >= 4 -> true ; writeln(nodiff(Word1,Word2,Diffs)),!,fail),!,
   reverse(Word1,Word1R),
   getAssWordC(Word2,Word2C),
   countDiffs(Word1R,Word2C,DiffsRC),!,
   (DiffsRC >= 4 -> true ; writeln(nodiffRC(Word1,Word2,DiffsRC)),!,fail),!,
   verifyDiffWords(Words,Word1).
verifyDiffWords([],_).


isGoodWord(Word):-!,
      countCGs(Word,4),!,
      reverse(Word,WordR),
      getAssWordC(Word,WordC),
      countDiffs(WordR,WordC,Diffs),!,
      Diffs >= 4.


getAssWordC(['A'|Ls],['T'|NLs]):-getAssWordC(Ls,NLs).
getAssWordC(['T'|Ls],['A'|NLs]):-getAssWordC(Ls,NLs).
getAssWordC(['C'|Ls],['G'|NLs]):-getAssWordC(Ls,NLs).
getAssWordC(['G'|Ls],['C'|NLs]):-getAssWordC(Ls,NLs).
getAssWordC([],[]).


countCGs(Word,CGs):-
      countCGs(Word,0,CGs).
countCGs([L|Ls],I,CGs):-
      ((L='C' ; L='G') ->
          I1 is I + 1,
          countCGs(Ls,I1,CGs)
      ;
          countCGs(Ls,I,CGs)
      ).
countCGs([],CGs,CGs).


countDiffs(Word1,Word2,Diffs):-
      countDiffs(Word1,Word2,0,Diffs).

countDiffs([L|Word1],[L|Word2],I,Diffs):-!,
      countDiffs(Word1,Word2,I,Diffs).
countDiffs([_|Word1],[_|Word2],I,Diffs):-
      I1 is I + 1,
      countDiffs(Word1,Word2,I1,Diffs).
countDiffs([],[],Diffs,Diffs).