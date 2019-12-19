% Author: Amit Metodi
% Last Updated: 10/10/2015

:- module(bcVectorLex, [ ]).
:- use_module('../auxs/auxLiterals').

/*
 TODO:
  * Optimize the encoding for a series of constant "1" of the vector
    (constant "0" was optimized)
    For example:
    [A1,A2, 1, 1, 1,A6,A7] <= [B1,B2,B3,B4,B5,B6,B7]
    should not create "eq" bits for each location of the "1" -
    it can use encoding of "(-B3 or -B4 or -B5)<->Z" and use Z as single bit in the vector.
*/

:- Head=bool_arrays_lex(A,B,[bc(Type,[A,B])|Constrs]-Constrs),
   Body=(
       !,
       bcVectorLex:vectorsLEqType(Type)
   ),
   bParser:addConstraint(Head,Body).

:- Head=bool_arrays_lexLt(A,B,[bc(Type,[FA,FB])|Constrs]-Constrs),
   Body=(
       !,
       bcVectorLex:vectorsLexLt2Lex(A,B,FA,FB),
       bcVectorLex:vectorsLEqType(Type)
   ),
   bParser:addConstraint(Head,Body).


vectorsLexLt2Lex(A,B,FA,FB):-!,
   length(A,Alen),
   length(B,Blen),
   (Alen==Blen ->
       append(A,[ 1],FA),
       append(B,[-1],FB) ;
   (Alen<Blen ->
       Diff is Blen - Alen,
       length(Falses,Diff),
       auxLiterals:litAsgnFalses(Falses),
       append([A,Falses,[1]],FA),
       append(B,[-1],FB) ;
   %Alen>Blen
       Diff is Alen - Blen,
       length(Falses,Diff),
       auxLiterals:litAsgnFalses(Falses),
       append([B,Falses,[-1]],FB),
       append(A,[1],FA)
   )).

%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
vectorsLEqType([
              bcVectorLex:vectorLEqSimplify,
              bcVectorLex:vectorLEqSimplifyAdv,
              0,
              bcVectorLex:vectorLEq2cnf,
              vectorLex
             ]).

% --------------------------------
% | Simplify (A <= B)            |
% --------------------------------
vectorLEqSimplify(Constr, NewConstr, Changed):-!,
    Constr=bc(Type,[A,B]),
    simplifyvectorLEq_s1(A,B,NA,NB,Changed),
    (NA=[] ->
        Changed=1,
        NewConstr=none ;
    (NB=[] ->
        Changed=1,
        NewConstr=none,
        litAsgnFalses(NA) ;
    ((NB=[B0],NA=[A0]) ->
        lits2plits([B0,-A0],Vec),
        bcAtLeastOne:aloType(ALOType),
        bcAtLeastOne:aloSimplify(bc(ALOType,Vec),NewConstr,_) ;
    (Changed==1 ->
        NewConstr=bc(Type,[NA,NB]) ;
        NewConstr=Constr
    )))).

simplifyvectorLEq_s1([A|As],[B|Bs],NA,NB,Changed):-!,
   ((ground(A), A=:=1) ->
      Changed=1,
      litAsgnTrue(B),
      simplifyvectorLEq_s1(As,Bs,NA,NB,_) ;
   ((ground(B), B=:= -1) ->
      Changed=1,
      litAsgnFalse(A),
      simplifyvectorLEq_s1(As,Bs,NA,NB,_) ;
   lit2plit(A,Al,Aop),
   lit2plit(B,Bl,Bop),
   (Al==Bl ->
      (Aop==Bop ->
          Changed=1,
          simplifyvectorLEq_s1(As,Bs,NA,NB,Changed)
      ;
          ((As=[], Bs=[]) ; Changed=1),!,
          NA=[A],
          NB=[B]
      ) ;
   NA=[A|As],
   NB=[B|Bs]
   ))).
simplifyvectorLEq_s1([],[],[],[],_Changed):-!.
simplifyvectorLEq_s1([],[_|_],[],[],1):-!.
simplifyvectorLEq_s1(A,[],A,[],_):-!.

% --------------------------------
% | Advance Simplify (A =< B)     |
% --------------------------------

vectorLEqSimplifyAdv(Constr, NewConstr, Changed):-!,
    Constr=bc(Type,[As,Bs]),
    simplifyvectorLEq_adv(As,Bs,NAs,NBs,Changed),!,
    simplifyvectorLEq_cut(NAs,NBs,MAs,MBs,Changed),!,
    simplifyvector_LEq_longdisEq(MAs,MBs,FAs,FBs,ChangedEq),!,
    (ChangedEq==1 ->
        Changed=1,
        vectorLEqSimplify(bc(Type,[FAs,FBs]), NewConstr, _)
    ;
    (Changed==1 ->
        vectorLEqSimplify(bc(Type,[MAs,MBs]), NewConstr, _)
    ;
        NewConstr=Constr
    )).

/*
   Advance Simplify:
  * Move contants to B vector:
   [A1..Aj, 1,Aj+2..An] <= [B1..Bj, X,Bj+2..Bn]
   -->
   [A1..Aj,-B,Aj+2..An] <= [B1..Bj,-1,Bj+2..Bn]
  * remove equal values:
   [A1..Aj,X,Aj+2..An] <= [B1..Bj,X,Bj+2..Bn]
   -->
   [A1..Aj,  Aj+2..An] <= [B1..Bj,  Bj+2..Bn]
  * Cut vectors when:
    [...,-1,...]<=[..., 1,...]
    or
    [..., 1,...]<=[...,-1,...]
*/
simplifyvectorLEq_adv([A|As],[B|Bs],NAs,NBs,Changed):-!,
   (ground(A) ->
       (\+ ground(B) ->
           Changed=1,
           NAs=[-B|MAs],
           NBs=[-A|MBs],
           simplifyvectorLEq_adv(As,Bs,MAs,MBs,Changed) ;
       (B=:=A ->
           Changed=1,
           simplifyvectorLEq_adv(As,Bs,NAs,NBs,Changed) ;
       (B=:=1 -> % and A\==B -> A=-1
           Changed=1,
           NAs=[],
           NBs=[] ;
       % B=-1, A=1
       NAs=[A],
       NBs=[B],
       ((As=[],Bs=[]) ; Changed=1),!
       ))) ;
   (litIsEqual(A,B) ->
       Changed=1,
       simplifyvectorLEq_adv(As,Bs,NAs,NBs,Changed) ;
    NAs=[A|MAs],
    NBs=[B|MBs],
    simplifyvectorLEq_adv(As,Bs,MAs,MBs,Changed)
    )).
simplifyvectorLEq_adv([],[],[],[],_Changed):-!.
simplifyvectorLEq_adv([],[_|_],[],[],1):-!.
simplifyvectorLEq_adv([A|As],[],NAs,NBs,1):-!,
    length(As,Len1),
    Len is Len1 + 1,
    length(Bs,Len),
    litAsgnFalses(Bs),!,
    simplifyvectorLEq_adv([A|As],Bs,NAs,NBs,_Changed).


/*
   Find the index of the last sequance of X in a vector.
   (X must be 1 or -1)
*/
findLastSeqIndex([A|As],X,VIndx,CSIndx,SIndx):-!,
   VIndx1 is VIndx + 1,
   ((ground(A), A =:= X) ->
       (CSIndx == -1 ->
           findLastSeqIndex(As,X,VIndx1,VIndx,SIndx)
       ;
           findLastSeqIndex(As,X,VIndx1,CSIndx,SIndx)
       )
   ;
       findLastSeqIndex(As,X,VIndx1,-1,SIndx)
   ).
findLastSeqIndex([],_X,_VIndx,SIndx,SIndx):-!.


/*
   Advance Simplify:
  * Remove tailing 1s in B
   [A1..Aj,Aj+1..An] <= [B1..Bj,1..1]
   -->
   [A1..Aj] <= [B1..Bj]
   
   Note: the case:
   [A1..Aj,-1..-1] <= [B1..Bj,Bj+1..Bn]
   isn't possible because during simplifyvectorLEq_adv
   we move constants from A to B.
*/

simplifyvectorLEq_cut(As,Bs,NAs,NBs,Changed):-!,
    findLastSeqIndex(Bs, 1,0,-1,Bindx1),
    (Bindx1 == -1 ->
        findLastSeqIndex(As, 1,0,-1,Aindx1),
        (Aindx1 == -1 ->
            NAs=As, NBs=Bs
        ;
            findLastSeqIndex(Bs, -1,0,-1,Bindx0),
            (Bindx0 == Aindx1 ->
                NAs=As, NBs=Bs
            ;
                !,Bindx0 < Aindx1, % Must be true
                Changed=1,
                auxLists:listKeepFrom(Bindx0,Bs,TBs),
                auxLists:listKeepFrom(Bindx0,As,TAs),
                append(TBs,[-1],NBs),
                append(TAs,[1],NAs),!
            )
        )
    ;
        Changed=1,
        auxLists:listKeepFrom(Bindx1,Bs,NBs),
        auxLists:listKeepFrom(Bindx1,As,NAs)
    ).



/*
   Advance Simplify:
   [X1,A,X2,B,X3]
   <=lex
   [Y1,B,Y2,A,Y3]
   ->
   [X1,A,X2,X3]
   <=lex
   [Y1,B,Y2,Y3]
or
   [X1,A,X2,A,X3]
   <=lex
   [Y1,B,Y2,B,Y3]
   ->
   [X1,A,X2,X3]
   <=lex
   [Y1,B,Y2,Y3]
   
*/
simplifyvector_LEq_longdisEq([_],[_],_,_,_):-!.
simplifyvector_LEq_longdisEq([X|Xs],[Y|Ys],NXs,NYs,Changed):-!,
    simplifyvector_LEq_longdisEq(Xs,Ys,TXs,TYs,ChangedRest),!,
    (ChangedRest==1 ->
        Changed=1,
        simplifyvector_LEq_longdisEq(X,Y,TXs,TYs,ZXs,ZYs,HasN),!,
        (HasN==1 ->
            NXs=[X|ZXs],
            NYs=[Y|ZYs]
        ;
            NXs=[X|TXs],
            NYs=[Y|TYs]
        )
    ;
        simplifyvector_LEq_longdisEq(X,Y,Xs,Ys,ZXs,ZYs,HasN),!,
        (HasN==1 ->
            Changed=1,
            NXs=[X|ZXs],
            NYs=[Y|ZYs]
        ;
            true
        )
    ).
simplifyvector_LEq_longdisEq([],[],_,_,_):-!.


simplifyvector_LEq_longdisEq(A,B,[X|Xs],[Y|Ys],NXs,NYs,HasN):-!,
   simplifyvector_LEq_longdisEq(A,B,Xs,Ys,TXs,TYs,HasN),
   (auxLiterals:litIsEqual(A,X) ->
       (auxLiterals:litIsEqual(B,Y) -> Drop=1 ; true) ;
   (auxLiterals:litIsEqual(A,Y) ->
       (auxLiterals:litIsEqual(B,X) -> Drop=1 ; true) ;
   true
   )),!,
   (Drop==1 ->
       (HasN==1 ->
           NXs=TXs,
           NYs=TXs
       ;
           NXs=Xs,
           NYs=Ys,
           HasN=1
       )
   ;
      (HasN==1 ->
          NXs=[X|TXs],
          NYs=[Y|TYs]
      ;
          true
      )
   ).
simplifyvector_LEq_longdisEq(_,_,[],[],_,_,_):-!.

% --------------------------------
% | CNF                          |
% --------------------------------
vectorLEq2cnf(bc(_,[As,Bs]),CnfH-CnfT):-
    vecGEqvecCnf_(Bs,As,CnfH-CnfT).

% A >= B (Eim1=1)
vecGEqvecCnf_([Ai|As],[Bi|Bs],CnfH-CnfT):-!,
    ((ground(Ai), Ai =:= 1) ->
%         (collectMore1s(As,Bs,OBs,RAs,RBs) ->
%             leading1sCnf([Bi|OBs],Ei,CnfH-CnfM),
%             vecGEqvecCnf_(RAs,RBs,Ei,CnfM-CnfT)
%         ;
            vecGEqvecCnf_(As,Bs,Bi,CnfH-CnfT)
%         )
    ;
        CnfH=[
              [ Ai,-Bi],     % B=1 -> A=1    (11, 01*)
              [-Ai, Bi,-Ei], % A=1 & B=0 -> Ei=0     (10)
              [ Ai, Ei],     % A=0 -> Ei=1   (00 , 01*)
              [-Bi, Ei]      % B=1 -> Ei=1   (11 , 01*)
              |CnfM],
        vecGEqvecCnf_(As,Bs,Ei,CnfM-CnfT)
    ).
vecGEqvecCnf_([Ai],[Bi],Eim1,CnfH-CnfT):-!,
    ((ground(Ai), Ai=:= -1) ->
        CnfH=[[-Eim1, -Bi]|CnfT]
    ;
        CnfH=[[-Eim1, Ai, -Bi]|CnfT]
    ).
vecGEqvecCnf_([Ai|As],[Bi|Bs],Eim1,CnfH-CnfT):-!,
    ((ground(Ai), abs(Ai)=:=1) ->
        (Ai =:= 1 ->
            CnfH=[[Eim1, -Ei],     % (Ei-1)=0 -> Ei=0
                  [Bi,-Ei],        % A=1 & B=0 -> Ei=0     (10)
                  [-Bi,-Eim1, Ei]  % B=1 & Ei-1=1 -> Ei=1   (11 , 01*)
                  |CnfM],
            vecGEqvecCnf_(As,Bs,Ei,CnfM-CnfT)
        ;
            CnfH=[[ -Bi,-Eim1]    % B=1 -> Ei=0     (01)
                  |CnfM],
            vecGEqvecCnf_(As,Bs,Eim1,CnfM-CnfT)
        )
    ;
        CnfH=[[Eim1, -Ei],       % (Ei-1)=0 -> Ei=0
              [ Ai,  -Bi,-Eim1], % A=0 & B=1 -> Eim1=0 / Ei=0     (01)
              [-Ai,   Bi,-Ei],   % A=1 & B=0 -> Ei=0    (10)
              [ Ai,-Eim1, Ei],   % A=0 & Ei-1=1 -> Ei=1   (00 , 01*)
              [-Bi,-Eim1, Ei]    % B=1 & Ei-1=1 -> Ei=1   (11 , 01*)
              |CnfM],
        vecGEqvecCnf_(As,Bs,Ei,CnfM-CnfT)
    ).

vecGEqvecCnf_(As,Bs,Eim1,CnfH-CnfT):-!, %% happens when advance simplify is turn off and |As|!=|Bs|
   length(As,Alen),
   length(Bs,Blen),
   !,Alen =\= Blen,!,
   (Alen<Blen ->
       Diff is Blen - Alen,
       length(Falses,Diff),
       auxLiterals:litAsgnFalses(Falses),
       append(As,Falses,FAs),
       vecGEqvecCnf_(FAs,Bs,Eim1,CnfH-CnfT) ;
   %Alen>Blen
       CnfH=CnfT
   ).
   
%%% handle the constant "1" part of the vector
% collectMore1s([A|As],Bs,OBs,RAs,RBs):-!,
%    ground(A), A=:=1,!,
%    Bs=[B|MBs],
%    OBs=[B|MOBs],
%    collectMore1s_(As,MBs,MOBs,RAs,RBs).
% collectMore1s_([A|As],Bs,OBs,RAs,RBs):-
%    ground(A), A=:=1,!,
%    Bs=[B|MBs],
%    OBs=[B|MOBs],
%    collectMore1s_(As,MBs,MOBs,RAs,RBs).
% collectMore1s_(As,Bs,[],As,Bs):-!.
% 
% 
% leading1sCnf(Bs,Ei,CnfH-CnfT):-!,
%    litNotXs(Bs,NBs),
%    CnfM=[[Ei|NBs]|CnfT],
%    leading1sCnf_(Bs,-Ei,CnfH-CnfM).
% leading1sCnf_([A|As],X,[[A,X]|CnfH]-CnfT):-!,
%     leading1sCnf_(As,X,CnfH-CnfT).
% leading1sCnf_([],_,Cnf-Cnf):-!.