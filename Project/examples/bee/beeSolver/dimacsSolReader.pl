% Author: Amit Metodi
% Date: 30/12/2011

:- module(dimacsSolReader, [
               sol2numbersAVL/2,
               sol2posNumbersAVL/2,
                                    getLitValFromAVL/3,
                                    getLitsValsFromAVL/3,
               sol2negNumbersAVL/2, getLitValFromNegAVL/3,
               readSolFile2AVL/3,   % readSolFile2AVL(Filename, Sol2AVLpredicate, SolAVL)
                                    % can be one of { sol2numbersAVL / sol2posNumbersAVL / sol2negNumbersAVL }
               readMinSolFile2AVL/3
               ]).

readSolFile2AVL(Filename, Sol2AVLpredicate, SolAVL):-!,
    open(Filename,read,FID),!,
    readSolFile2AVL_(FID,Sol2AVLpredicate, SolAVL),
    close(FID).

readSolFile2AVL_(FID, Sol2AVLpredicate, SolAVL):-!,
    read_line_to_codes(FID, Line),!,
    (Line = [83, 65, 84|_] -> % SAT
        read_line_to_codes(FID, Line2),!,
        call(Sol2AVLpredicate,Line2,AVL),
        SolAVL=(sat,AVL) ;
    (Line = [68, 79, 78, 69|_] -> % DONE
        SolAVL=(done,none) ;
    (Line = [85, 78, 83, 65, 84|_] -> % UNSAT
        SolAVL=(unsat,none) ;
    (Line = [99|_] -> % comments
%         writef('c: %s\n',[Line]),!,
        readSolFile2AVL_(FID, Sol2AVLpredicate, SolAVL) ;
    ((Line==end_of_file ; Line = [84, 73, 77, 69, 79, 85, 84 | _])  -> % TimeOut
        SolAVL=(timeout,none) ;
%         writef('unknown line: %s\n',[Line]),!,
    SolAVL=(error,none)
    ))))).


readMinSolFile2AVL(Filename, Sol2AVLpredicate, SolAVL):-
    open(Filename,read,FID),
    readMinSolFile2AVL_(FID,Sol2AVLpredicate, none, SolAVL),
    close(FID).

readMinSolFile2AVL_(FID, Sol2AVLpredicate, PrevAVL, SolAVL):-
    read_line_to_codes(FID, Line),!,
    (Line = [83, 65, 84|_] -> % SAT
        read_line_to_codes(FID, Line2),!,
        call(Sol2AVLpredicate,Line2,CurAVL),
        readMinSolFile2AVL_(FID, Sol2AVLpredicate, CurAVL, SolAVL) ;
    (Line = [68, 79, 78, 69|_] -> % DONE
        (PrevAVL==none ->
            SolAVL=(done,none)
        ;
            SolAVL=(sat,PrevAVL)
        ) ;
    (Line = [85, 78, 83, 65, 84|_] -> % UNSAT
        (PrevAVL==none ->
            SolAVL=(unsat,none)
        ;
            SolAVL=(sat,PrevAVL)
        ) ;
    (Line = [99|_] -> % comments
%        writef('c: %s\n',[Line]),!,
        readMinSolFile2AVL_(FID, Sol2AVLpredicate, PrevAVL, SolAVL) ;
    ((Line==end_of_file ; Line = [84, 73, 77, 69, 79, 85, 84 | _])  -> % TimeOut
        SolAVL=(timeout,PrevAVL) ;
%        writef('unknown line: %s\n',[Line]),!,
    SolAVL=(error,PrevAVL)
    ))))).



sol2numbersAVL(String,NumbersAVL):-
    sol2numbersAVL(String,CodeNum-CodeNum,t, NumbersAVL).


% white space (space)
sol2numbersAVL([32|String], []-[], CurAVL, NumbersAVL):-!,
    sol2numbersAVL(String, CodeNum-CodeNum, CurAVL, NumbersAVL).
sol2numbersAVL([32|String], CodeNum-[], CurAVL, NumbersAVL):-!,
    number_codes(Num, CodeNum),
    NumKey is abs(Num),
    NumVal is sign(Num),!,
    put_assoc(NumKey, CurAVL, NumVal, CurAVL1),!,
    sol2numbersAVL(String, NCodeNum-NCodeNum, CurAVL1, NumbersAVL).
% part of number
sol2numbersAVL([Chr|String], CodeNumH-[Chr|CodeNumT], CurAVL, NumbersAVL):-!,
    sol2numbersAVL(String, CodeNumH-CodeNumT, CurAVL, NumbersAVL).

% end of line
sol2numbersAVL([],[]-[],NumbersAVL,NumbersAVL):-!.
sol2numbersAVL([],CodeNum-[],CurAVL,NumbersAVL):-!,
    number_codes(Num, CodeNum),
    NumKey is abs(Num),
    NumVal is sign(Num),
    put_assoc(NumKey, CurAVL, NumVal, NumbersAVL).
         
         
         
         
         
         
         
         
         
         
         
         
         
sol2posNumbersAVL(String,NumbersAVL):-
    sol2posNumbersAVL(String,CodeNum-CodeNum,t, NumbersAVL).


% white space (space)
sol2posNumbersAVL([32|String], []-[], CurAVL, NumbersAVL):-!,
    sol2posNumbersAVL(String, CodeNum-CodeNum, CurAVL, NumbersAVL).
sol2posNumbersAVL([32|String], CodeNum-[], CurAVL, NumbersAVL):-!,
    number_codes(Num, CodeNum),
    NumVal is sign(Num),!,
    (NumVal == 1 ->
         NumKey is abs(Num),
         put_assoc(NumKey, CurAVL, NumVal, CurAVL1),!,
         sol2posNumbersAVL(String, NCodeNum-NCodeNum, CurAVL1, NumbersAVL)
    ;
         sol2posNumbersAVL(String, NCodeNum-NCodeNum, CurAVL, NumbersAVL)
    ).
% part of number
sol2posNumbersAVL([Chr|String], CodeNumH-[Chr|CodeNumT], CurAVL, NumbersAVL):-!,
    sol2posNumbersAVL(String, CodeNumH-CodeNumT, CurAVL, NumbersAVL).

% end of line
sol2posNumbersAVL([],[]-[],NumbersAVL,NumbersAVL):-!.
sol2posNumbersAVL([],CodeNum-[],CurAVL,NumbersAVL):-!,
    number_codes(Num, CodeNum),
    NumVal is sign(Num),
    (NumVal == 1 ->
        NumKey is abs(Num),
        put_assoc(NumKey, CurAVL, NumVal, NumbersAVL)
    ;
        NumbersAVL=CurAVL).
             
             
             
             


sol2negNumbersAVL(String,NumbersAVL):-
    sol2negNumbersAVL(String,CodeNum-CodeNum,t, NumbersAVL).


% white space (space)
sol2negNumbersAVL([32|String], []-[], CurAVL, NumbersAVL):-!,
    sol2negNumbersAVL(String, CodeNum-CodeNum, CurAVL, NumbersAVL).
sol2negNumbersAVL([32|String], CodeNum-[], CurAVL, NumbersAVL):-!,
    number_codes(Num, CodeNum),
    NumVal is sign(Num),!,
    (NumVal == -1 ->
        NumKey is abs(Num),
        put_assoc(NumKey, CurAVL, NumVal, CurAVL1),!,
        sol2negNumbersAVL(String, NCodeNum-NCodeNum, CurAVL1, NumbersAVL)
    ;
        sol2negNumbersAVL(String, NCodeNum-NCodeNum, CurAVL, NumbersAVL)
    ).
% part of number
sol2negNumbersAVL([Chr|String], CodeNumH-[Chr|CodeNumT], CurAVL, NumbersAVL):-!,
    sol2negNumbersAVL(String, CodeNumH-CodeNumT, CurAVL, NumbersAVL).

% end of line
sol2negNumbersAVL([],[]-[],NumbersAVL,NumbersAVL):-!.
sol2negNumbersAVL([],CodeNum-[],CurAVL,NumbersAVL):-!,
    number_codes(Num, CodeNum),
    NumVal is sign(Num),
    (NumVal == -1 ->
        NumKey is abs(Num),
        put_assoc(NumKey, CurAVL, NumVal, NumbersAVL)
    ;
        NumbersAVL=CurAVL).

             
             
             
             
getLitValFromAVL(Num,AVL,Value):-!,
    NumKey is abs(Num),!,
    get_posassoc(NumKey,AVL,AVLval),!,
    Value is AVLval * sign(Num).

get_posassoc(Key, t(K,V,_,L,R), Val) :-!,
    compare(Rel, Key, K),!,
    get_posassoc(Rel, Key, V, L, R, Val).
get_posassoc(_, t, -1) :-!.

get_posassoc(=, _, Val, _, _, Val):-!.
get_posassoc(<, Key, _, Tree, _, Val) :-!,
    get_posassoc(Key, Tree, Val).
get_posassoc(>, Key, _, _, Tree, Val) :-!,
    get_posassoc(Key, Tree, Val).



getLitsValsFromAVL([X|Xs],AVL,[V|Vs]):-!,
    getLitValFromAVL(X,AVL,V),!,
    getLitsValsFromAVL(Xs,AVL,Vs).
getLitsValsFromAVL([],_,[]):-!.




getLitValFromNegAVL(Num,AVL,Value):-!,
    NumKey is abs(Num),!,
    get_negassoc(NumKey,AVL,AVLval),!,
    Value is AVLval * sign(Num).

get_negassoc(Key, t(K,V,_,L,R), Val) :-!,
    compare(Rel, Key, K),!,
    get_negassoc(Rel, Key, V, L, R, Val).
get_negassoc(_, t, 1) :-!.

get_negassoc(=, _, Val, _, _, Val):-!.
get_negassoc(<, Key, _, Tree, _, Val) :-!,
    get_negassoc(Key, Tree, Val).
get_negassoc(>, Key, _, _, Tree, Val) :-!,
    get_negassoc(Key, Tree, Val).
