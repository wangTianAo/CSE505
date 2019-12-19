% Author: Amit Metodi
% Date: 12/05/2012

:- module(aMap, [
                 newMap/1,
                 addToMap/3,
                 getFromMap/3
                ]).
                
newMap(map(Map)):-
    empty_assoc(Map).

addToMap(Key,Map,Value):-
    Map=map(CurMap),
    put_assoc(Key, CurMap, Value, UpdMap),
    setarg(1,Map,UpdMap).
getFromMap(Key,map(Map),Value):-
    get_assoc(Key, Map, Value).