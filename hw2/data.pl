myClause(1, or(a_1, a_2)).

myClause(2, or(or(neg(a_2), b_2), b_3)).

myClause(3, or(neg(b_2), b_3)).

myClause(4, neg(b_3)).

myQuery(5, a_1).