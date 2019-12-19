% Author: Amit Metodi
% Date: 12/01/2011

:- module('auxGraphs', [
                generateGraph/4,
                generateConnectedGraph/4,
                generateConnectedWeightedGraph/6,
                generateCompleteGraph/3,
                isConnectedGraph/1
                ]).

generateGraph(N,E,I,graph(ID,N,E,Es)):-
   concat_atom(['g',I,'_',N,'x',E],ID),
   generateEdges(E,N,[],USEs),
   sort(USEs,Es).

generateConnectedGraph(N,E,I,Graph):-
   generateGraph(N,E,I,Graph1),!,
   (isConnectedGraph(Graph1) ->
       Graph=Graph1
   ;
       generateConnectedGraph(N,E,I,Graph)
   ).

generateConnectedWeightedGraph(N,E,I,WMin,WMax,Graph):-!,
   generateConnectedGraph(N,E,I,Graph1),!,
   addWeightsToGraph(Graph1,WMin,WMax,Graph).

generateCompleteGraph(N,I,graph(ID,N,E,Es)):-
   E is (N*(N-1))/2,
   concat_atom(['g',I,'_',N,'x',E],ID),
   completeEdges(1,2,N,Es).


%%% ---- Generate Graph ---- %%%

randomEdge(N,(I,J)):-!,
   X is random(N*(N-1)),
   I1 is X mod N + 1,
   J1 is X // N + 1,
   (J1==I1 -> J2=N ; J2=J1),
   I is min(I1,J2),
   J is max(I1,J2).

generateEdges(0,_,Es,Es):-!.
generateEdges(E,N,SoFarEs,Es):-!,
   repeat,
   randomEdge(N,Edge),
   \+ member(Edge,SoFarEs),
   E1 is E - 1,
   generateEdges(E1,N,[Edge|SoFarEs],Es).

%%% ---- Check for connected graph ---- %%%

isConnectedGraph(graph(_,N,_M,Es)):-!,
    collectEs_vs([1],Es,[]),!,
    verticesInEdges(Es,AVs),!,
    sort(AVs,Vs),!,
    length(Vs,N),!,
    append([[1],_,[N]],Vs).

collectEs(V,[(V,X)|Es],Vs,REs,LeftEs):-!,
    collectEs(V,Es,[X|Vs],REs,LeftEs).
collectEs(V,[(X,V)|Es],Vs,REs,LeftEs):-!,
    collectEs(V,Es,[X|Vs],REs,LeftEs).
collectEs(V,[(X,Y)|Es],Vs,REs,LeftEs):-
    (X<V),!,
    collectEs(V,Es,Vs,[(X,Y)|REs],LeftEs).
collectEs(_V,Es,Vs,REs,LeftEs):-!,
    append(REs,Es,NREs),!,
    (Vs==[] -> LeftEs=NREs ;
    sort(Vs,SVs),
    collectEs_vs(SVs,NREs,LeftEs)).

collectEs_vs([V|Vs],Es,LeftEs):-!,
   collectEs(V,Es,[],[],REs),!,
   collectEs_vs(Vs,REs,LeftEs).
collectEs_vs([],LeftEs,LeftEs):-!.


verticesInEdges([(X,Y)|Es],[X,Y|Vs]):-!,
    verticesInEdges(Es,Vs).
verticesInEdges([],[]):-!.

%%% ---- Add Weights to graph ---- %%%

addWeightsToGraph(graph(ID,N,E,Es),Min,Max,graph(WID,N,E,WEs)):-!,
    atom_concat('w',ID,WID),
    Max1 is Max + 1,
    addWeightsToEdges(Es,Min,Max1,WEs).
    
    
addWeightsToEdges([(I,J)|Es],Min,Max1,[(I,J,W)|WEs]):-!,
    random(Min,Max1,W),
    addWeightsToEdges(Es,Min,Max1,WEs).
addWeightsToEdges([],_,_,[]):-!.



%%% ---- Complete graph Edges ---- %%%

completeEdges(N,_,N,[]):-!.
completeEdges(I,N,N,[(I,N)|Es]):-!,
    I1 is I + 1,
    J is I1 + 1,
    completeEdges(I1,J,N,Es).
completeEdges(I,J,N,[(I,J)|Es]):-!,
    J1 is J + 1,
    completeEdges(I,J1,N,Es).

