% Vertex Magic Total Labelings
% Author: Amit Metodi
% Date: 06/05/2012

:- module('vmtl', [ solveVmtl/2 ]).

:- use_module('../auxs/auxRunExpr',[runExpr/5, decodeInt/2]).

/*
  Usage:
  ------
  ?- Instance=vmtl(Graph,K), solveVmtl(Instance,Solution).

  Where Graph=graph(ID,Vcnt,Ecnt,Es) :
     ID : atom - graph ID
     Vcnt : integer - amount of vertices in graph (1..Vcnt)
     Ecnt : integer - amount of edges in graph
     Es : List of touples representing edges (I,J)

  Paper Example:
  --------------
  ?- vmtl:example(Instance), solveVmtl(Instance,Solution).

*/

example(Instance):-
    Instance=vmtl(Graph,K),
    K=14,
    Graph=graph(ex1,4,4,[(1,2),(1,3),(2,3),(3,4)]).

solveVmtl(Instance,Solution):-!,
    printInstance(Instance),
    runExpr(Instance,Solution,
            vmtl:encode,
            vmtl:decode,
            vmtl:verify).

printInstance(vmtl(graph(GraphID,_,_,_),K)):-
    writef('%5r,%3r,',[GraphID,K]),flush_output.


%%% ENCODE

encode(vmtl(graph(_,N,M,Es),K), map(VsLabels,EsLabels), Constraints):-!,
   MaxLabel is N + M,
   createVs(N,MaxLabel,VsLabels,Constraints-Constraints1,VBits),!,
   createEs(Es,MaxLabel,EsLabels,Constraints1-Constraints2,EBits),!,
   verteciesWeights(VsLabels,EsLabels,K,Constraints2-Constraints3),
   append(VBits,EBits,AllBits),!,
   Constraints3=[int_array_allDiff(AllBits)].

createVs(0,_,[],Constraints-Constraints,[]):-!.
createVs(I,Label,[(I,IBits)|VsLabels],[new_int(IBits,1,Label)|ConstraintsH]-ConstraintsT,[IBits|VBits]):-!,
    I1 is I - 1,
    createVs(I1,Label,VsLabels,ConstraintsH-ConstraintsT,VBits).

createEs([],_,[],Constraints-Constraints,[]):-!.
createEs([(I,J)|Es],Label,[(I,J,IJBits)|EsLabels],[new_int(IJBits,1,Label)|ConstraintsH]-ConstraintsT,[IJBits|EBits]):-!,
    createEs(Es,Label,EsLabels,ConstraintsH-ConstraintsT,EBits).

verteciesWeights([],_,_,Constrs-Constrs):-!.
verteciesWeights([(I,IBits)|VsLabels],EsLabels,KBits,[int_array_plus([IBits|EBits],KBits)|ConstrsH]-ConstrsT):-!,
    findEs(EsLabels,I,EBits),!,
    verteciesWeights(VsLabels,EsLabels,KBits,ConstrsH-ConstrsT).

findEs([(X,_,_)|_],I,[]):-X>I,!.
findEs([(I,_,IJBits)|EsLabels],I,[IJBits|EBits]):-!,
    findEs(EsLabels,I,EBits).
findEs([(_,I,IJBits)|EsLabels],I,[IJBits|EBits]):-!,
    findEs(EsLabels,I,EBits).
findEs([_|EsLabels],I,EBits):-!,
    findEs(EsLabels,I,EBits).
findEs([],_,[]):-!.

%%% DECODE
decode(map(VsLabels,EsLabels), Solution):-
    decodeVertexLabeling(VsLabels,Solution-Solution1),!,
    decodeEdgeLabeling(EsLabels,Solution1-[]).

decodeVertexLabeling([(Id,Iint)|VsLabels],[label(vertex(Id),Ival)|LabelingH]-LabelingT):-!,
    decodeInt(Iint,Ival),
    decodeVertexLabeling(VsLabels,LabelingH-LabelingT).
decodeVertexLabeling([],Solution-Solution):-!.

decodeEdgeLabeling([(I,J,IJint)|EsLabels],[label(edge(I,J),IJval)|LabelingH]-LabelingT):-!,
    decodeInt(IJint,IJval),
    decodeEdgeLabeling(EsLabels,LabelingH-LabelingT).
decodeEdgeLabeling([],Solution-Solution):-!.


%%% VERIFY

verify(vmtl(graph(_,N,M,Es),K),Labeling):-!,
    MaxLabel is N+M,!,
    length(Labeling,MaxLabel),!,
    checkVertexLabel(N,MaxLabel,Labeling),!,
    checkEdgeLabel(Es,MaxLabel,Labeling),!,
    checkContainsAllLabels(MaxLabel,Labeling),!,
    checkVMTL(N,Labeling,K).

checkVertexLabel(0,_,_):-!.
checkVertexLabel(I,MaxLabel,Labeling):-!,
     member(label(vertex(I),L),Labeling),!,
     L>0, L=<MaxLabel,
     I1 is I - 1,
     checkVertexLabel(I1,MaxLabel,Labeling).

checkEdgeLabel([],_,_):-!.
checkEdgeLabel([(I,J)|Es],MaxLabel,Labeling):-!,
     member(label(edge(I,J),L),Labeling),!,
     L>0, L=<MaxLabel,
     checkEdgeLabel(Es,MaxLabel,Labeling).

checkContainsAllLabels(0,_):-!.
checkContainsAllLabels(I,Labeling):-!,
      member(label(_,I),Labeling),!,
      I1 is I - 1,
      checkContainsAllLabels(I1,Labeling).

checkVMTL(0,_,_):-!.
checkVMTL(I,Labeling,K):-!,
      findall(S,(member(label(edge(I,_),S),Labeling) ; member(label(edge(_,I),S),Labeling)),Sums),!,
      member(label(vertex(I),SL),Labeling),!,
      sumList([SL|Sums],0,K),!,
      I1 is I - 1,
      checkVMTL(I1,Labeling,K).

sumList([],K,K):-!.
sumList([X|Xs],SoFar,K):-!,
     SoFar1 is SoFar + X,
     sumList(Xs,SoFar1,K).
