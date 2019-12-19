% Author: Amit Metodi
% Last Updated: 19/05/2017

:- module(bcInteger, [ ]).
:- use_module('../auxs/auxLiterals').
:- use_module('../auxs/auxUnarynum').
:- use_module('../auxs/auxDirectnum').

/*
  Known Issues:
  * After unifying two integers, channeling/valid number will be encoded twice.
*/

%%% ------------------------- %%%
%%% add constraints to parser %%%
%%% ------------------------- %%%
:- Head=new_int(A,Min,Max,[bc(Type,A)|Constrs]-Constrs),
   Body=(
        !,
         (var(A) ->
             ((integer(Min),integer(Max)) ->
                 auxUnarynum:unarynumNewInRange(Min,Max,(Min,Max,UData)),
                 A=(int,Min,Max,[(order,UData)|_]),
                 (Min+1 < Max ; bcInteger:getDirectNumber(A,_)),!,
                 bcInteger:integerType(Type)
             ;
                 throw(model_err(new_int,'Min and/or Max are not constant integers !'))
             )
         ;
             throw(model_err(new_int,'the variable was already defined !'))
         )
   ),
   bParser:addConstraint(Head,Body).

:- Head=new_int_direct(A,Min,Max,[bc(Type,A)|Constrs]-Constrs),
   Body=(
       !,
         (var(A) ->
             ((integer(Min),integer(Max)) ->
                 auxDirectnum:directnumNewInRange(Min,Max,(Min,Max,UData)),
                 A=(int,Min,Max,[(direct,UData)|_]),
                 (Min+1 < Max ; bcInteger:getUnaryNumber(A,_)),!,
                 bcInteger:integerType(Type)
             ;
                 throw(model_err(new_int,'Min and Max must be constant integers !'))
             )
         ;
             throw(model_err(new_int,'The variable was already defined !'))
         )
   ),
   bParser:addConstraint(Head,Body).

:- Head=new_direct(A,Min,Max,ConstrsH-ConstrsT),   %%% Alias for not breaking existing models
   Body=(!,bParser:new_int_direct(A,Min,Max,ConstrsH-ConstrsT)),
   bParser:addConstraint(Head,Body).

   
:- Head=new_int_dual(A,Min,Max,[bc(Type,A)|Constrs]-Constrs),
   Body=(
        !,
         (var(A) ->
             ((integer(Min),integer(Max)) ->
                 auxUnarynum:unarynumNewInRange(Min,Max,(Min,Max,UData)),
                 A=(int,Min,Max,[(order,UData)|_]),
                 bcInteger:getDirectNumber(A,_),
                 bcInteger:integerType(Type)
             ;
                 throw(model_err(new_int,'Min and Max must be constant integers !'))
             )
         ;
             throw(model_err(new_int,'The variable was already defined !'))
         )
   ),
   bParser:addConstraint(Head,Body).

:- Head=new_int(A,Dom,[bc(Type,A)|Constrs]-Constrs),
   Body=(
        !,
         auxUnarynum:unarynumNewInDomain(Dom,(Min,Max,UData)),
         A=(int,Min,Max,[(order,UData)|_]),
         bcInteger:integerType(Type)
   ),
   bParser:addConstraint(Head,Body).

:- Head=new_int_direct(A,Dom,[bc(Type,A)|Constrs]-Constrs),
   Body=(
        !,
         auxDirectnum:directnumNewInDomain(Dom,(Min,Max,UData)),
         A=(int,Min,Max,[(direct,UData)|_]),
         (Min+1 < Max ; bcInteger:getUnaryNumber(A,_)),!,
         bcInteger:integerType(Type)
   ),
   bParser:addConstraint(Head,Body).


:- Head=bool2int(Bool,Int,Constrs-Constrs),
   Body=(
        !,
         UData=([Bool],Bool),
         DData=([-Bool,Bool],[Bool,-Bool]),
         BInt=(int,0,1,[(order,UData),(direct,DData)|_]),
         (var(Int) ->
             Int=BInt
         ;
             bcInteger:unifyNumbers(Int,BInt)
         )
   ),
   bParser:addConstraint(Head,Body).

:- Head=int_eq(A,B,Constrs-Constrs),
   Body=(
        !,
         bcInteger:unifyNumbers(A,B)
   ),
   bParser:addConstraint(Head,Body).


%%% ------------------------- %%%
%%%   Define Temp Variables   %%%
%%% ------------------------- %%%
:- Head=new_temp_int(A,Min,Max,ConstrsH-ConstrsT),
   Body=(!,bParser:new_int(A,Max,Min,ConstrsH-ConstrsT)),
   bParser:addConstraint(Head,Body).

:- Head=new_temp_int(A,Dom,ConstrsH-ConstrsT),
   Body=(!,bParser:new_int(A,Dom,ConstrsH-ConstrsT)),
   bParser:addConstraint(Head,Body).

:- Head=new_temp_int_direct(A,Min,Max,ConstrsH-ConstrsT),
   Body=(!,bParser:new_int_direct(A,Max,Min,ConstrsH-ConstrsT)),
   bParser:addConstraint(Head,Body).

:- Head=new_temp_int_direct(A,Dom,ConstrsH-ConstrsT),
   Body=(!,bParser:new_int_direct(A,Dom,ConstrsH-ConstrsT)),
   bParser:addConstraint(Head,Body).

:- Head=new_temp_int_dual(A,Min,Max,ConstrsH-ConstrsT),
   Body=(!,bParser:new_int_dual(A,Max,Min,ConstrsH-ConstrsT)),
   bParser:addConstraint(Head,Body).

%%% ------------------------- %%%
%%% constraints types         %%%
%%% ------------------------- %%%
integerType([
        bcInteger:intSimplify,
        0,
        0,
        0,
        integer
       ]):-!.


intSimplify(bc(_,Integer),Constr,Changed):-!,
    (haveUnaryNumber(Integer) ->
        getUnaryNumber(Integer,(_,_,UBits,_)),
        (\+ haveDirectNumber(Integer) ->
            bcSorted:sortedType(SortType),
            bcSorted:sortedSimplify(bc(SortType,UBits),Constr, Changed)
        ;
            getDirectNumber(Integer,(_,_,DBits,_)),
            lits2plits(DBits,DPBits),
            bcUnaryDirectChnl:chnlU2DType(ChnlType),
            bcUnaryDirectChnl:unary2directSimplify(bc(ChnlType,[[1|UBits],[-1|DBits],[(1,-1)|DPBits]]), Constr, Changed)
        )
    ;
        (getDirectNumber(Integer,(_,_,DBits,_)) ->
            auxLiterals:lits2plits([-1|DBits],PBits),
            bcExactlyOne:exoType(ExoType),
            bcExactlyOne:exoSimplify(bc(ExoType,PBits), Constr, Changed)
        ;
            throw(model_err('defined int variable without order or direct representations !')) % should never happen
        )
    ),!,
    closeNumberRepList(Integer).



%%% Auxiliary %%%

closeNumberRepList(Integer):-
    Integer=(int,_Min,_Max,Reps),
    closeNumberRepList_aux(Reps).
closeNumberRepList_aux([]):-!.
closeNumberRepList_aux([_|Rs]):-!,
    closeNumberRepList_aux(Rs).

haveNumberRep(Reps,RType):-!,
   \+ var(Reps),
   Reps=[CRep|MReps],
   (CRep=(RType,_) ; !,haveNumberRep(MReps,RType)).

haveUnaryNumber(X):-var(X),!, throw(model_err('undefined int variable !')).
haveUnaryNumber((int,_,_,Reps)):-!, haveNumberRep(Reps,order).
haveUnaryNumber(-Y):-!,haveUnaryNumber(Y).
haveUnaryNumber(X):-!,integer(X).

haveDirectNumber(X):-var(X),!, throw(model_err('undefined int variable !')).
haveDirectNumber((int,_,_,Reps)):-!, haveNumberRep(Reps,direct).
haveDirectNumber(-Y):-!,haveDirectNumber(Y).
haveDirectNumber(X):-!,integer(X).

getNumberRep(Reps,RType,RData):-!,
    \+ var(Reps),
    Reps=[CRep|MReps],
    (CRep=(RType,RData) ; !, getNumberRep(MReps,RType,RData)).

addNumberRep(Reps,Rep):-!,
    (var(Reps) ->
        Reps=[Rep|_]
    ;
        Reps=[_|MReps],
        addNumberRep(MReps,Rep)
    ).
        
getUnaryNumber(X,_):-var(X),!, throw(model_err('undefined int variable !')).
getUnaryNumber((int,Min,Max,Reps),Z):-!,
    (getNumberRep(Reps,order,UData) ->
        Z=(Min,Max,UData) ;
    (haveNumberRep(Reps,direct) -> % add channeling
        auxUnarynum:unarynumNewInRange(Min,Max,Z),
        Z=(Min,Max,UData),
        addNumberRep(Reps,(order,UData)),!
    ;
        throw(model_err('int does not have order representation ! ',(int,Min,Max,Reps)))
    )).
getUnaryNumber(Const,(Const,Const,[],1)):-integer(Const),!.
getUnaryNumber(-(X),_):-var(X),!, throw(model_err('undefined int variable !')).
getUnaryNumber(-(-X),Z):-!,getUnaryNumber(X,Z).
getUnaryNumber(-(X),Z):-!,
    getUnaryNumber(X,Z0),!,
    auxUnarynum:unarynumNeg(Z0,Z).
getUnaryNumber(X,_):-!, throw(model_err('int does not have order representation ! ',X)).

getUnaryNumbers([A|As],[Au|Aus]):-!,
    getUnaryNumber(A,Au),
    getUnaryNumbers(As,Aus).
getUnaryNumbers([],[]):-!.


getDirectNumber(X,_):-var(X),!, throw(model_err('undefined int variable !')).
getDirectNumber((int,Min,Max,Reps),Z):-!,
    (getNumberRep(Reps,direct,DData) ->
        Z=(Min,Max,DData) ;
    (haveNumberRep(Reps,order) -> % add channeling
        auxDirectnum:directnumNewInRange(Min,Max,Z),
        Z=(Min,Max,UData),
        addNumberRep(Reps,(direct,UData))
    ;
        throw(model_err('int does not have direct representation ! ',(int,Min,Max,Reps)))
    )).
getDirectNumber(Const,(Const,Const,[1],[1])):-integer(Const),!.
getDirectNumber(-(X),_):-var(X),!, throw(model_err('undefined int variable !')).
getDirectNumber(-(-X),Z):-!,getDirectNumber(X,Z).
getDirectNumber(-(X),ND):-!,
    getDirectNumber(X,D),!,
    auxDirectnum:directnumNeg(D,ND).
getDirectNumber(X,_):-!, throw(model_err('int does not have direct representation ! ',X)).

getDirectNumbers([A|As],[Ad|AsD]):-!,
    getDirectNumber(A,Ad),
    getDirectNumbers(As,AsD).
getDirectNumbers([],[]):-!.
    
unifyNumbers(A,B):-!,
    ((haveUnaryNumber(A),haveUnaryNumber(B)) ->
        unifyUnaries(A,B),
        ((haveDirectNumber(A),haveDirectNumber(B)) ->
            unifyDirects(A,B)
        ;
            true
        )
    ;
    ((haveDirectNumber(A),haveDirectNumber(B)) ->
        unifyDirects(A,B)
    ;
        throw(int_eq_failed(A,B))
    )).

unifyUnaries(A,B):-!,
    getUnaryNumber(A,Au),
    getUnaryNumber(B,Bu),!,
    auxUnarynum:unarynumEquals(Au,Bu).

unifyDirects(A,B):-!,
    getDirectNumber(A,Ad),
    getDirectNumber(B,Bd),
    auxDirectnum:directnumEquals(Ad,Bd).
    
    
    
getIntMinMax(Int,_,_):-var(Int),!, throw(model_err('undefined int variable !')).
getIntMinMax((int,Min,Max,_),Min,Max):-!.
getIntMinMax(-Int,Min,Max):-!,
    getIntMinMax(Int,MMin,MMax),!,
    Min is -MMax,
    Max is -MMin.
getIntMinMax(Int,Min,Max):-
    integer(Int),!,
    Min=Int,
    Max=Int.
    
getIntsSumMinMax(Ints,Min,Max):-!,
    getIntsSumMinMax(Ints,0,0,Min,Max).
getIntsSumMinMax([],Min,Max,Min,Max):-!.
getIntsSumMinMax([Int|MInts],CMin,CMax,FMin,FMax):-!,
    bcInteger:getIntMinMax(Int,Min,Max),!,
    NCMin is CMin + Min,
    NCMax is CMax + Max,
    getIntsSumMinMax(MInts,NCMin,NCMax,FMin,FMax).