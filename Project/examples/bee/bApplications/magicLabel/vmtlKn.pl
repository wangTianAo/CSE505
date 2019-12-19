% Vertex Magic Total Labelings for Kn graphs
% Author: Amit Metodi
% Date: 06/05/2012

:- module('vmtlKn', [ solveVmtlKn/2 ]).

:- use_module('../auxs/auxRunExpr',[runExpr/5]).
:- use_module('../auxs/auxGraphs',[generateCompleteGraph/3]).
:- use_module(vmtl).

/*
  Usage:
  ------
  ?- N=8, K=155 ,Instance=vmtlKn(N,K), solveVmtlKn(Instance,Solution).

*/

solveVmtlKn(Instance,Solution):-!,
    printInstance(Instance),
    Instance=vmtlKn(N,K),
    generateCompleteGraph(N,k,Graph),
    FixInstance=vmtl(Graph,K),
    runExpr(FixInstance,Solution,
            vmtlKn:encode,
            vmtl:decode,
            vmtl:verify).

printInstance(vmtlKn(N,K)):-
    writef('K%3l,%3r,',[N,K]),flush_output.

encode(Instance, Map, Constraints):-!,
    vmtl:encode(Instance, Map, Constraints1),
    %%% Symmetry Breaking for complete graphs
    vtmlKnSymmetryBreak(Map,Constraints2),
    append(Constraints1,Constraints2,Constraints).

vtmlKnSymmetryBreak(map(_VsLabels,EsLabels),Constrs):-
   collectEdgesLabels(1,1,EsLabels,E1s),
   E1s=[_E12,E13|_],
   sortedEs(E1s,Constrs-Constrs1),
   collectEdgesLabels(2,2,EsLabels,E2s),
   allGreaterThan(E2s,E13,Constrs1-[]).

collectEdgesLabels(I,J,Es,[Eij|RelEs]):-
    J1 is J + 1,
    member((I,J1,Eij),Es),!,
    collectEdgesLabels(I,J1,Es,RelEs).
collectEdgesLabels(_,_,_,[]):-!.

sortedEs([E1,E2|Es],[int_lt(E1,E2)|GroupH]-GroupT):-!,
    sortedEs([E2|Es],GroupH-GroupT).
sortedEs([_],Group-Group):-!.

allGreaterThan([E2j|E2s],E12,[int_lt(E12,E2j)|GroupH]-GroupT):-!,
    allGreaterThan(E2s,E12,GroupH-GroupT).
allGreaterThan([],_,Group-Group):-!.
