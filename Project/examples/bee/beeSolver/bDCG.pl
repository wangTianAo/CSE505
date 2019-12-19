% Author: Amit Metodi
% Last Update: 24/08/2016

:- module(bDCG, [
                        whiteSpace/2,
                        constraint/3,
                        solveGoal/3
                        ]).

whiteSpace -->
    [32], % space
    whiteSpace.
whiteSpace -->
    [9], % tab
    whiteSpace.
whiteSpace --> [].

underscore(95) -->
    [95].
upperLetter(X) -->
    [X],
    {X >= 65, X =< 90}.
lowerLetter(X) -->
    [X],
    {X >= 97, X =< 122}.
digit(X) -->
    [X],
    {X >= 48, X =< 57}.

intConst(X) -->
    (digit(D0) ; ("-",{ D0=45 })),
    intConst_(Ds),
    {number_codes(X,[D0|Ds])}.
intConst_([X|Xs]) -->
    digit(X),
    intConst_(Xs).
intConst_([]) --> [].


varParId(ID) -->
    varParId1(IDstr),
    { atom_codes(ID,IDstr) }.
varParId1([X|VarId]) -->
    underscore(X),
    varParId1(VarId).
varParId1([X|VarId]) -->
    (upperLetter(X) ;
     lowerLetter(X)),
    varParId2(VarId).
varParId2([X|VarId]) -->
    (upperLetter(X) ;
     lowerLetter(X) ;
     digit(X) ;
     underscore(X)),
     varParId2(VarId).
varParId2([]) --> [].


expr(X) -->
    (
     varParIdAdv(X) ;
     ("-", varParIdAdv(Z), {X= -Z})  ;
     intConst(X) ;
     arrayExpr(X)
    ).

exprs([X|Xs]) -->
   whiteSpace,
   expr(X),
   whiteSpace,
   ((",",exprs(Xs)) ;
    { Xs=[] }).

arrayExpr(X) -->
   whiteSpace,
   "[",
   (exprs(X) ;
    whiteSpace, {X=[]}),
   "]".


varParIdAdv(X) -->
    varParId(VarIdT),
    (
     ("[",intConst(VarIdIndx),"]", {
      X=nth(VarIdIndx,VarIdT)
     } )
    ;
     { X=VarIdT }
    ).

predAnnId(ID) -->
    (upperLetter(X) ;
     lowerLetter(X)),
    varParId2(IDstr),
    { atom_codes(ID,[X|IDstr]) }.


constraint((ConstrId,Exprs)) -->
    predAnnId(ConstrId),
    "(",
    exprs(Exprs),
    ")".

%% Special case for new_int(X,Dom)
constraint((Constr,[Var,Dom])) -->
    predAnnId(Constr),
    "(",
    whiteSpace,
    expr(Var),
    whiteSpace,
    ",",
    whiteSpace,
    "[",
    domain(Dom),
    "]",
    whiteSpace,
    ")".        

domain([X|Xs]) -->
   whiteSpace,
   domain_interval(X),
   whiteSpace,
   ((",",domain(Xs)) ;
    { Xs=[] }). 
domain_interval(X) -->
    domain_val(S),
    (
      ("-",domain_val(E),{X=S-E})
    ;
      {X=S}
    ).

domain_val(X) -->
    intConst(X).
domain_val(X) -->
    "(",
    intConst(X),
    ")".

solveGoal(Goal) -->
    "solve",
    whiteSpace,
    solveGoal_(Goal).
solveGoal_(satisfy(X)) -->
    "satisfy(",
    intConst(X),
    ")".
solveGoal_(satisfy) -->
    "satisfy".
solveGoal_(minimize(VarId)) -->
    "minimize",
    whiteSpace,
    varParIdAdv(VarId).
solveGoal_(maximize(VarId)) -->
    "maximize",
    whiteSpace,
    varParIdAdv(VarId).
