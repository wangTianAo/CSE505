% Author: Amit Metodi
% Last Updated: 01/07/2012

:- module(bcUnaryDiff, [ ]).
:- use_module('../auxs/auxLiterals').


:- Head=int_neq(A,B,ConstrsH-ConstrsT),
   Body=(
       !,
       bcInteger:getUnaryNumber(A,Au),
       bcInteger:getUnaryNumber(B,Bu),
       bcUnaryDiff:unaryDiffType(Type),
       bcUnaryDiff:unaryDiffSimplify(bc(Type,[Au,Bu]),Constr, 1),
       (Constr==none ->
           ConstrsH=ConstrsT
       ;
           ConstrsH=[Constr|ConstrsT]
       )
   ),
   bParser:addConstraint(Head,Body).


%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
unaryDiffType([
               bcUnaryDiff:unaryDiffSimplify,
               bcUnaryDiff:unaryDiffSimplifyAdv,
               0,
               bcUnaryDiff:unaryDiff2cnf,
               unaryDiff]).

% ---------------------------------
% | Reduce Diffrent Unaries       |
% ---------------------------------

unaryDiffSimplify(Constr,NewConstr, Changed):-!,
    Constr=bc(Type,[A,B]),
    auxUnarynum:unarynumIsChangedOrConst(A,FA,Changed),
    auxUnarynum:unarynumIsChangedOrConst(B,FB,Changed),!,
    (Changed==1 ->
        FA=(Amin,Amax,_),
        FB=(Bmin,Bmax,_),
        ((Amin > Bmax ; Amax < Bmin) ->
            NewConstr=none ;
        (Amin==Amax ->
            NewConstr=none,
            auxUnarynum:unarynumDiffK(FB,Amin) ;
        (Bmin==Bmax ->
            NewConstr=none,
            auxUnarynum:unarynumDiffK(FA,Bmin) ;
        (Amin==Bmax ->
            FA=(_,_,[Ab|_],_),
            FB=(_,_,_,Bb),
            lits2plits([Ab,-Bb],Vec),
            bcAtLeastOne:aloType(ALOtype),
            bcAtLeastOne:aloSimplify(bc(ALOtype,Vec),NewConstr,_) ;
        (Amax==Bmin->
            FB=(_,_,[Bb|_],_),
            FA=(_,_,_,Ab),
            lits2plits([-Ab,Bb],Vec),
            bcAtLeastOne:aloType(ALOtype),
            bcAtLeastOne:aloSimplify(bc(ALOtype,Vec),NewConstr,_) ;
        (Amin==Bmin ->
            Dmin=Amin
            ;
            Dmin is max(Amin,Bmin) - 1
        ),
        (Amax==Bmax ->
            Dmax=Amax
        ;
            Dmax is min(Amax,Bmax) + 1
        ),
        auxUnarynum:unarynumFocusOn(FA,Dmin,Dmax,NA),
        auxUnarynum:unarynumFocusOn(FB,Dmin,Dmax,NB),
        NewConstr=bc(Type,[NA,NB])
        )))))
    ;
        NewConstr=Constr
    ).


unaryDiffSimplifyAdv(Constr,NewConstr, Changed):-!,
    Constr=bc(Type,[A,B]),
    auxUnarynum:unarynumIsChangedOrConst(A,FA,Changed),
    auxUnarynum:unarynumIsChangedOrConst(B,FB,Changed),!,
    (Changed==1 ->
        unaryDiffSimplify(bc(Type,[FA,FB]),NewConstr, 1) ;
    A=(Os1,_,Abits,_),
    B=(Os2,_,Bbits,_),
    (Os1==Os2 ->
        reduceDiffUnry_s1(Abits,Bbits,NAbits,NBbits,Changed,Keep) ;
    (Os1>Os2 ->
        reduceDiffUnry_s1([1|Abits],Bbits,NAbits,NBbits,Changed,Keep) ;
        reduceDiffUnry_s1(Abits,[1|Bbits],NAbits,NBbits,Changed,Keep)
    )),!,
    (Keep==0 ->
        Changed=1,
        NewConstr=none ;
    (NAbits=[] ->
        throw(unsat) ;
    ((NAbits=[X],NBbits=[Y]) ->
        Changed=1,
        NewConstr=none,
        litUnify(X,-Y) ;
    (Changed==1 ->
        auxUnarynum:unarynumFromList(NAbits,NA),
        auxUnarynum:unarynumFromList(NBbits,NB),
        unaryDiffSimplify(bc(Type,[NA,NB]),NewConstr, 1)
    ;
        NewConstr=Constr
    ))))).




%%% Assumes that |U1min - U2min| <= 1 and |U1max - U2max| <= 1
reduceDiffUnry_s1([U1],[U2],_,_,1,0):-!,
    litUnify(U1,-U2).
reduceDiffUnry_s1([U1|Us1],[U2|Us2], NUs1, NUs2, Changed, Keep):-!,
    lit2plit(U1,U1l,U1op),
    lit2plit(U2,U2l,U2op),!,
    (U1l==U2l ->
        (U1op==U2op -> % (true,true) / (A,A) (can't be (false/false)
            Changed=1,
            litAsgnTrue(U1),
            reduceDiffUnry_s1(Us1, Us2, NUs1, NUs2, Changed, Keep)
        ;
            Keep=0
        )
    ;
        reduceDiffUnry_s2(Us1,(U1,U1op,U1l),Us2,(U2,U2op,U2l), NUs1, NUs2, Changed, Keep)
    ).
reduceDiffUnry_s1([U1],[], _, _, 1, 0):-!,
    litAsgnTrue(U1).
reduceDiffUnry_s1([],[U2], _, _, 1, 0):-!,
    litAsgnTrue(U2).

reduceDiffUnry_s2([U12|Us1],(U11,U11op,U11l),[U22|Us2],(U21,U21op,U21l), NUs1, NUs2, Changed, Keep):-!,
    lit2plit(U12,U12l,U12op),!,
    ((U11l==U12l , U11op \== U12op) -> % U1=[A,-A]
        Keep=0, Changed=1,
        litAsgnTrue(U11),
        litUnify(U21,U22) ;
    lit2plit(U22,U22l,U22op),!,
    ((U21l==U22l , U21op \== U22op) -> % U2=[A,-A]
        Keep=0, Changed=1,
        litAsgnTrue(U21),
        litUnify(U11,U12) ;
    ((U12l==U22l, U12op\==U22op) -> Keep=0 ; % [?,A],[?,-A]
    ((U11l==U22l, U21l==U12l) ->
        ((U11op\==U22op, U21op\==U12op) -> % [A,B],[-B,-A] -> [A,A],[-A,-A]
            Keep=0, Changed=1,
            litUnify(U11,U12) ;
        ((U11op==U22op, U21op\==U12op) -> % [A,B],[-B,A] -> [A,0],[1,A]
            Keep=0, Changed=1,
            litAsgnFalse(U12) ;
        ((U11op\==U22op, U21op==U12op) -> % [A,B],[B,-A] -> [1,B],[B,0]
            Keep=0, Changed=1,
            litAsgnTrue(U11) ;
%       ((U11op==U22op, U21op==U12op) -> % [A,B],[B,A] -> [A,A],[A,A]
            litUnify(U11,U12,Changed),
            reduceDiffUnry_s2(Us1,(U12,U12op,U12l),Us2,(U22,U22op,U22l), NUs1, NUs2, Changed, Keep)
        ))) ;
    (((U12l==1 , U12op== -1) ; (U22l==1 , U22op== -1)) -> % [?,-1] (? != -1)
        (U12l==U22l ->
            NUs1=[U11],NUs2=[U21], Keep= 1
        ;
            NUs1=[U11,U12],NUs2=[U21,U22], Keep=1
        ) ;
    ((U12l==U22l ; (U11l==U12l , U21l==U22l)) ->
        reduceDiffUnry_s2(Us1,(U11,U11op,U11l),Us2,(U21,U21op,U21l), NUs1, NUs2, Changed, Keep) ;
    (((U11l==1, U11l==U12l) ; (U21l==1, U21l==U22l)) -> % (U11=U12=1) | (U21=U22=1)
        reduceDiffUnry_s2(Us1,(U12,U12op,U12l),Us2,(U22,U22op,U22l), NUs1, NUs2, Changed, Keep) ;
    NUs1=[U11|NNUs1],
    NUs2=[U21|NNUs2],
    reduceDiffUnry_s2(Us1,(U12,U12op,U12l),Us2,(U22,U22op,U22l), NNUs1, NNUs2, Changed, Keep)
    ))))))).
reduceDiffUnry_s2([],(U1,_,_),[],(U2,_,_),[U1], [U2], _, 1):-!.
reduceDiffUnry_s2([U12],(U11,U11op,U11l),[],(U21,U21op,U21l), NUs1, NUs2, Changed, Keep):-!,
    reduceDiffUnry_s2([U12],(U11,U11op,U11l),[-1],(U21,U21op,U21l), NUs1, NUs2, Changed, Keep).
reduceDiffUnry_s2([],(U11,U11op,U11l),[U22],(U21,U21op,U21l), NUs1, NUs2, Changed, Keep):-!,
    reduceDiffUnry_s2([-1],(U11,U11op,U11l),[U22],(U21,U21op,U21l), NUs1, NUs2, Changed, Keep).

% ---------- Different Unaries ----------

unaryDiff2cnf(bc(_,[A,B]),CnfH-CnfT):-!,
    A=(Amin,_,Abits,_),
    B=(Bmin,_,Bbits,_),
    (Amin==Bmin ->
        % no (A=0 & B=0)
        Abits=[A1|_],
        Bbits=[B1|_],
        CnfH=[[A1,B1]|CnfM],!,
        diffUnary2cnf_itr(Abits,Bbits,CnfM-CnfT) ;
    (Amin > Bmin ->
        Abits=[A2|_],
        Bbits=[B1,B2|Bbits3],
        CnfH=[[A2,-B1,B2]|CnfM],!,
        diffUnary2cnf_itr(Abits,[B2|Bbits3],CnfM-CnfT)
    ;
        Abits=[A1,A2|Abits3],
        Bbits=[B2|_],
        CnfH=[[-A1,A2,B2]|CnfM],!,
        diffUnary2cnf_itr([A2|Abits3],Bbits,CnfM-CnfT)
    )).

    
% no (A=10 & B=10)
diffUnary2cnf_itr([A1,A2|As],[B1,B2|Bs],[[-A1,A2,-B1,B2]|CnfH]-CnfT):-!,
    diffUnary2cnf_itr([A2|As],[B2|Bs],CnfH-CnfT).
diffUnary2cnf_itr([A1],[B1],[[-A1,-B1]|Cnf]-Cnf):-!.
diffUnary2cnf_itr([A1,A2],[B1],[[-A1,A2,-B1]|Cnf]-Cnf):-!.
diffUnary2cnf_itr([A1],[B1,B2],[[-A1,-B1,B2]|Cnf]-Cnf):-!.

