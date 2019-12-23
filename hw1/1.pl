split([],[],[]).
split(L,Odd,Even) :- odd(L,Odd,Even).

odd([],[],[]).
odd([X|T],[X|Odd],Even) :- even(T,Odd,Even).

even([],[],[]).
even([X|T],Odd,[X|Even]) :- odd(T,Odd,Even).