% BEE constraints list check

% Author: Amit Metodi
% Last Update: 20/05/2017

:- module(bCheck, [checkConstraints/1]).

checkConstraints(Constrs):-!,
    \+ \+ checkConstraints(Constrs,0).

checkConstraints([Ci|Cs],PI):-!,
    I is PI + 1,
    checkConstraint(Ci,I),!,
    checkConstraints(Cs,I).
checkConstraints([],Cnt):-!,
    writef('%w constraints checked.\n',[Cnt]).

checkConstraint(Ci,I):-!,
    Ci =.. [Cname|Cargs],
    ((Cname=new_int ; Cname=new_temp_int ; Cname=new_int_direct ; Cname=new_temp_int_direct) -> % Special case new_int(X,Min,Max) and new_int(X,Dom)
        checkNewIntArgs(Cargs,I) ;
    (supportConstraint(Cname,ReqCargs) ->
        length(Cargs,CargsLen),
        length(ReqCargs,ReqCargsLen),
        (CargsLen==ReqCargsLen ->
            (checkConstraintsArgs(Cargs,ReqCargs,1,I) ->
                supportConstraintAdv(Ci,I)
            ;
                true
            )
        ;
            writef('Constraint #%w: Wrong amount of arguments.\n',[I])
        )
    ;
        writef('Constraint #%w: unknown constraint (%w).\n',[I,Cname])
    )).
    

checkConstraintsArgs([Aj|Args],[Atypej|Atypes],J,I):-!,
    call(Atypej,Aj,J,I),!,
    J1 is J + 1,
    checkConstraintsArgs(Args,Atypes,J1,I).
checkConstraintsArgs([],[],_,_):-!.

isUndefInt(X,_,_):-
    var(X),!,
    X=int.
isUndefInt(X,_,_):-
    integer(X),!.
isUndefInt(-X,J,I):-!,
    isUndefInt(X,J,I).
isUndefInt(X,J,I):-!,
    writef('Constraint #%w: argument #%w is not an undefined integer (%w).\n',[I,J,X]),
    !,fail.

isInt(X,J,I):-
    var(X),!,
    writef('Constraint #%w: argument #%w is undefined.\n',[I,J]),
    !,fail.
isInt(int,_,_):-!.
isInt(X,_,_):-
    integer(X),!.
isInt(-X,J,I):-!,
    isInt(X,J,I).
isInt(X,J,I):-!,
    writef('Constraint #%w: argument #%w is not an integer (%w).\n',[I,J,X]),
    !,fail.

isUndefBool(X,J,I):-
    isBool(X,J,I).
/*
isBool(X,J,I):-
    var(X),!,
    X=bool.
*/
isBool(bool,_,_):-!.
isBool(1,_,_):-!.
isBool(-1,_,_):-!.
isBool(-X,J,I):-!,
    isBool(X,J,I).
isBool(X,J,I):-!,
    writef('Constraint #%w: argument #%w is not a boolean (%w).\n',[I,J,X]),
    !,fail.
    
isConst(X,_,_):-
    integer(X),!.
isConst(X,J,I):-
    \+ var(X), X= -(Y),!,
    isConst(Y,J,I).
isConst(X,J,I):-!,
    writef('Constraint #%w: argument #%w is not a constant number (%w).\n',[I,J,X]),
    !,fail.

isListBool(Bs,J,I):-!,
    isListBool(Bs,J,I,1).
isListBool([B|Bs],J,I,Z):-!,
    concat_atom([J,'[',Z,']'],JZ),
    isBool(B,JZ,I),
    Z1 is Z + 1,
    isListBool(Bs,J,I,Z1).
isListBool([],_,_,_):-!.

isListInt(Bs,J,I):-!,
    isListInt(Bs,J,I,1).
isListInt([B|Bs],J,I,Z):-!,
    concat_atom([J,'[',Z,']'],JZ),
    isInt(B,JZ,I),
    Z1 is Z + 1,
    isListInt(Bs,J,I,Z1).
isListInt([],_,_,_):-!.

isListConst(Bs,J,I):-!,
    isListConst(Bs,J,I,1).
isListConst([B|Bs],J,I,Z):-!,
    concat_atom([J,'[',Z,']'],JZ),
    isConst(B,JZ,I),
    Z1 is Z + 1,
    isListConst(Bs,J,I,Z1).
isListConst([],_,_,_):-!.

isDomain(X,_,_):-
    \+ var(X),
    isDomain_aux(X).
isDomain(X,J,I):-!,
    writef('Constraint #%w: argument #%w is not a domain (%w).\n',[I,J,X]),
    !,fail.

isDomain_aux([V|Dom]):-!,
    \+ var(v),
    isDomain_val(V),!,
        isDomain_aux(Dom).
isDomain_aux([]):-!.
isDomain_val(V):-integer(V).
isDomain_val(V):- \+ var(V), V=(-X),!, isDomain_val(X).
isDomain_val(V):- \+ var(V), V=(S-E),!, integer(S), integer(E).

checkNewIntArgs([V,Min,Max],I):-!,
    isUndefInt(V,1,I),
    isConst(Min,2,I),
    isConst(Max,3,I).
checkNewIntArgs([V,Domain],I):-!,
    isUndefInt(V,1,I),
    isDomain(Domain,2,I).
checkNewIntArgs(_,I):-
    writef('Constraint #%w: Wrong amount of arguments.\n',[I]).

supportConstraint(new_bool,[isUndefBool]):-!.
supportConstraint(new_temp_bool,[isUndefBool]):-!.
%supportConstraint(new_int,[isUndefInt,isConst,isConst]):-!.
%supportConstraint(new_int,[isUndefInt,isDomain]):-!.
supportConstraint(new_int_dual,[isUndefInt,isConst,isConst]):-!.
%supportConstraint(new_int_direct,[isUndefInt,isConst,isConst]):-!.
%supportConstraint(new_int_direct,[isUndefInt,isDomain]):-!.
supportConstraint(new_direct,[isUndefInt,isConst,isConst]):-!.  %%% alias
%supportConstraint(new_temp_int,[isUndefInt,isConst,isConst]):-!.
%supportConstraint(new_temp_int,[isUndefInt,isDomain]):-!.
supportConstraint(new_temp_int_dual,[isUndefInt,isConst,isConst]):-!.
%supportConstraint(new_temp_int_direct,[isUndefInt,isConst,isConst]):-!.
%supportConstraint(new_temp_int_direct,[isUndefInt,isDomain]):-!.
supportConstraint(bool2int,[isBool,isUndefInt]):-!.

supportConstraint(new_int_plusK,[isUndefInt,isInt,isConst]):-!.
supportConstraint(new_int_direct_plusK,[isUndefInt,isInt,isConst]):-!.
supportConstraint(new_int_dual_plusK,[isUndefInt,isInt,isConst]):-!.
supportConstraint(new_int_mulK,[isUndefInt,isInt,isConst]):-!.
supportConstraint(new_int_divK,[isUndefInt,isInt,isConst]):-!.

supportConstraint(bool_eq,[isBool,isBool]):-!.
supportConstraint(bool_array_eq_reif,[isListBool,isBool]):-!.
supportConstraint(bool_array_or,[isListBool]):-!.
supportConstraint(bool_array_or_reif,[isListBool,isBool]):-!.
supportConstraint(bool_or_reif,[isBool,isBool,isBool]):-!.
supportConstraint(bool_array_and,[isListBool]):-!.
supportConstraint(bool_array_and_reif,[isListBool,isBool]):-!.
supportConstraint(bool_and_reif,[isBool,isBool,isBool]):-!.
supportConstraint(bool_array_xor,[isListBool]):-!.
supportConstraint(bool_array_xor_reif,[isListBool,isBool]):-!.
supportConstraint(bool_xor_reif,[isBool,isBool,isBool]):-!.
supportConstraint(bool_array_iff,[isListBool]):-!.
supportConstraint(bool_array_iff_reif,[isListBool,isBool]):-!.
supportConstraint(bool_iff_reif,[isBool,isBool,isBool]):-!.
supportConstraint(bool_ite,[isBool,isBool,isBool]):-!.
supportConstraint(bool_ite_reif,[isBool,isBool,isBool,isBool]):-!.

supportConstraint(bool_array_sum_eq,[isListBool,isInt]):-!.
supportConstraint(bool_array_sum_leq,[isListBool,isInt]):-!.
supportConstraint(bool_array_sum_geq,[isListBool,isInt]):-!.
supportConstraint(bool_array_sum_lt,[isListBool,isInt]):-!.
supportConstraint(bool_array_sum_gt,[isListBool,isInt]):-!.

supportConstraint(bool_array_pb_eq,[isListConst,isListBool,isInt]):-!.
supportConstraint(bool_array_pb_leq,[isListConst,isListBool,isInt]):-!.
supportConstraint(bool_array_pb_geq,[isListConst,isListBool,isInt]):-!.
supportConstraint(bool_array_pb_lt,[isListConst,isListBool,isInt]):-!.
supportConstraint(bool_array_pb_gt,[isListConst,isListBool,isInt]):-!.

supportConstraint(bool_array_sum_modK,[isListBool,isConst,isInt]):-!.
supportConstraint(bool_array_sum_divK,[isListBool,isConst,isInt]):-!.
supportConstraint(bool_array_sum_divModK,[isListBool,isConst,isInt,isInt]):-!.

supportConstraint(bool_arrays_eq,[isListBool,isListBool]):-!.
supportConstraint(bool_arrays_neq,[isListBool,isListBool]):-!.
supportConstraint(bool_arrays_eq_reif,[isListBool,isListBool,isBool]):-!.
supportConstraint(bool_arrays_neq_reif,[isListBool,isListBool,isBool]):-!.
supportConstraint(bool_arrays_lex,[isListBool,isListBool]):-!.
supportConstraint(bool_arrays_lexLt,[isListBool,isListBool]):-!.
supportConstraint(bool_arrays_lex_reif,[isListBool,isListBool,isBool]):-!.
supportConstraint(bool_arrays_lexLt_reif,[isListBool,isListBool,isBool]):-!.

supportConstraint(bool_arrays_eq,[isListBool,isListBool]):-!.
supportConstraint(bool_arrays_neq,[isListBool,isListBool]):-!.
supportConstraint(bool_arrays_eq_reif,[isListBool,isListBool,isBool]):-!.
supportConstraint(bool_arrays_neq_reif,[isListBool,isListBool,isBool]):-!.

supportConstraint(int_eq,[isInt,isInt]):-!.
supportConstraint(int_neq,[isInt,isInt]):-!.
supportConstraint(int_leq,[isInt,isInt]):-!.
supportConstraint(int_geq,[isInt,isInt]):-!.
supportConstraint(int_lt,[isInt,isInt]):-!.
supportConstraint(int_gt,[isInt,isInt]):-!.
supportConstraint(int_eq_reif,[isInt,isInt,isBool]):-!.
supportConstraint(int_neq_reif,[isInt,isInt,isBool]):-!.
supportConstraint(int_leq_reif,[isInt,isInt,isBool]):-!.
supportConstraint(int_geq_reif,[isInt,isInt,isBool]):-!.
supportConstraint(int_lt_reif,[isInt,isInt,isBool]):-!.
supportConstraint(int_gt_reif,[isInt,isInt,isBool]):-!.
supportConstraint(int_array_allDiff,[isListInt]):-!.
supportConstraint(int_array_allDiff_reif,[isListInt,isBool]):-!.
supportConstraint(int_array_allDiffCond,[isListInt,isListBool]):-!.

supportConstraint(int_plus,[isInt,isInt,isInt]):-!.
supportConstraint(int_times,[isInt,isInt,isInt]):-!.
supportConstraint(int_div,[isInt,isInt,isInt]):-!.
supportConstraint(int_mod,[isInt,isInt,isInt]):-!.
supportConstraint(int_max,[isInt,isInt,isInt]):-!.
supportConstraint(int_min,[isInt,isInt,isInt]):-!.
supportConstraint(int_abs,[isInt,isInt]):-!.
supportConstraint(int_array_max,[isListInt,isInt]):-!.
supportConstraint(int_array_min,[isListInt,isInt]):-!.
supportConstraint(int_array_times,[isListInt,isInt]):-!.
supportConstraint(int_array_plus,[isListInt,isInt]):-!.

supportConstraint(int_array_sum_eq,[isListInt,isInt]):-!.
supportConstraint(int_array_sum_leq,[isListInt,isInt]):-!.
supportConstraint(int_array_sum_lt,[isListInt,isInt]):-!.
supportConstraint(int_array_sum_geq,[isListInt,isInt]):-!.
supportConstraint(int_array_sum_gt,[isListInt,isInt]):-!.

supportConstraint(int_array_sumCond_eq,[isListBool,isListInt,isInt]):-!.
supportConstraint(int_array_sumCond_leq,[isListBool,isListInt,isInt]):-!.
supportConstraint(int_array_sumCond_lt,[isListBool,isListInt,isInt]):-!.
supportConstraint(int_array_sumCond_geq,[isListBool,isListInt,isInt]):-!.
supportConstraint(int_array_sumCond_gt,[isListBool,isListInt,isInt]):-!.

supportConstraint(int_array_lin_eq,[isListConst,isListInt,isInt]):-!.
supportConstraint(int_array_lin_leq,[isListConst,isListInt,isInt]):-!.
supportConstraint(int_array_lin_lt,[isListConst,isListInt,isInt]):-!.
supportConstraint(int_array_lin_geq,[isListConst,isListInt,isInt]):-!.
supportConstraint(int_array_lin_gt,[isListConst,isListInt,isInt]):-!.

supportConstraint(int_array_sum_modK,[isListInt,isConst,isInt]):-!.
supportConstraint(int_array_sum_divK,[isListInt,isConst,isInt]):-!.
supportConstraint(int_array_sum_divModK,[isListInt,isConst,isInt,isInt]):-!.

supportConstraint(int_arrays_eq,[isListInt,isListInt]):-!.
supportConstraint(int_arrays_neq,[isListInt,isListInt]):-!.
supportConstraint(int_arrays_eq_reif,[isListInt,isListInt,isBool]):-!.
supportConstraint(int_arrays_neq_reif,[isListInt,isListInt,isBool]):-!.
supportConstraint(int_arrays_lex,[isListInt,isListInt]):-!.
supportConstraint(int_arrays_lexLt,[isListInt,isListInt]):-!.
supportConstraint(int_arrays_lex_reif,[isListInt,isListInt,isBool]):-!.
supportConstraint(int_arrays_lexLt_reif,[isListInt,isListInt,isBool]):-!.
supportConstraint(int_arrays_lex_implied,[isListInt,isListInt,isBool]):-!.
supportConstraint(int_arrays_lexLt_implied,[isListInt,isListInt,isBool]):-!.


supportConstraintAdv(int_array_allDiffCond(Ints,Bools),I):-!,
    length(Ints,L1),
    length(Bools,L2),
    (L1==L2 ; writef('Constraint #%w: arrays must be in the same length.\n',[I])),!.
supportConstraintAdv(int_array_lin_eq(Consts,Ints,_),I):-!,
    length(Consts,L1),
    length(Ints,L2),
    (L1==L2 ; writef('Constraint #%w: arrays must be in the same length.\n',[I])),!.
supportConstraintAdv(int_array_lin_leq(Consts,Ints,_),I):-!,
    length(Consts,L1),
    length(Ints,L2),
    (L1==L2 ; writef('Constraint #%w: arrays must be in the same length.\n',[I])),!.
supportConstraintAdv(int_array_lin_geq(Consts,Ints,_),I):-!,
    length(Consts,L1),
    length(Ints,L2),
    (L1==L2 ; writef('Constraint #%w: arrays must be in the same length.\n',[I])),!.
supportConstraintAdv(int_array_lin_lt(Consts,Ints,_),I):-!,
    length(Consts,L1),
    length(Ints,L2),
    (L1==L2 ; writef('Constraint #%w: arrays must be in the same length.\n',[I])),!.
supportConstraintAdv(int_array_lin_gt(Consts,Ints,_),I):-!,
    length(Consts,L1),
    length(Ints,L2),
    (L1==L2 ; writef('Constraint #%w: arrays must be in the same length.\n',[I])),!.
supportConstraintAdv(bool_array_pb_eq(Consts,Bits,_),I):-!,
    length(Consts,L1),
    length(Bits,L2),
    (L1==L2 ; writef('Constraint #%w: arrays must be in the same length.\n',[I])),!.
supportConstraintAdv(bool_array_pb_leq(Consts,Bits,_),I):-!,
    length(Consts,L1),
    length(Bits,L2),
    (L1==L2 ; writef('Constraint #%w: arrays must be in the same length.\n',[I])),!.
supportConstraintAdv(bool_array_pb_geq(Consts,Bits,_),I):-!,
    length(Consts,L1),
    length(Bits,L2),
    (L1==L2 ; writef('Constraint #%w: arrays must be in the same length.\n',[I])),!.
supportConstraintAdv(bool_array_pb_lt(Consts,Bits,_),I):-!,
    length(Consts,L1),
    length(Bits,L2),
    (L1==L2 ; writef('Constraint #%w: arrays must be in the same length.\n',[I])),!.
supportConstraintAdv(bool_array_pb_gt(Consts,Bits,_),I):-!,
    length(Consts,L1),
    length(Bits,L2),
    (L1==L2 ; writef('Constraint #%w: arrays must be in the same length.\n',[I])),!.

supportConstraintAdv(_,_):-!.