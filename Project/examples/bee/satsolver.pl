%% The SWI-Prolog interface to SAT solver

:- module(satsolver,[
                        sat/3,          sat/1,
                        satMulti/4,
                        satMaxUnary/4,  satMaxUnary/2,
                        satMinUnary/4,  satMinUnary/2,
                        satMinBinary/4, satMinBinary/2 %%% Binary is MSB first
                       ]).

errorMessage:- 
   writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),
   writeln('%               PL-SATsolver                  %'),
   writeln('%                                             %'),
   writeln('%   This satsolver.pl is a place holder !     %'),
   writeln('%   This file should be replaced with         %'),
   writeln('%   satsolver.pl from PL-SATsolver package    %'),
   writeln('%   and this folder should also contain at    %'),
   writeln('%   least one SAT solver shared library.      %'),
   writeln('%   The files can be obtained by compiling    %'),
   writeln('%   PL-SATsolver from satsolver_src folder    %'),
   writeln('%   (read the ReadMe file) or download the    %'),
   writeln('%   compiled DLLs for Windows from :          %'),
   writeln('% http://amit.metodi.me/research/plsatsolver/ %'),
   writeln('%                                             %'),
   writeln('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%').

:- errorMessage.   
                                           
sat(_):-errorMessage,!,fail.
sat(_,_,_):-errorMessage,!,fail.
satMulti(_,_,_,_):-errorMessage,!,fail.
satMinUnary(_,_):-errorMessage,!,fail.
satMaxUnary(_,_):-errorMessage,!,fail.
satMinUnary(_,_,_,_):-errorMessage,!,fail.
satMaxUnary(_,_,_,_):-errorMessage,!,fail.
satMinBinary(_,_):-errorMessage,!,fail.
satMinBinary(_,_,_,_):-errorMessage,!,fail.