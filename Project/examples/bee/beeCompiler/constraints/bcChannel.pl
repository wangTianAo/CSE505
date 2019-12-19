% Author: Amit Metodi
% Last Updated: 31/05/2017

:- module(bChannel, [ ]).

%% ----------- Channel order<->direct -------------------
:- Head=channel_int2direct(Int,Constrs-Constrs),
   Body=(!,
         bcInteger:getUnaryNumber(Int,_),
         bcInteger:getDirectNumber(Int,_)
        ),
   bParser:addConstraint(Head,Body).

:- Head=channel_direct2int(Int,Constrs-Constrs),
   Body=(!,
         bcInteger:getDirectNumber(Int,_),
         bcInteger:getUnaryNumber(Int,_)
        ),
   bParser:addConstraint(Head,Body).
   
% -------------- Channel to Vectors -------------
:- Head=int_order2bool_array(Int,BAry,BMin,ConstrsH-ConstrsT),
   Body=(!,
         (\+ var(Int) ->  % Int -> BAry
             bcInteger:getUnaryNumber(Int,(UMin,_UMax,UBits,_LBit)),
             ConstrsH=ConstrsT,!,
             (BMin=UMin ->
                 auxLiterals:litUnifiesWfalses(UBits,BAry)
             ;
                 (integer(BMin) ; throw(model_err(int_unary2bool_array,'Min is not an integer !'))),!,
                 (UMin > BMin ->
                     DD is UMin - BMin,
                     auxLists:listSplit(DD,BAry,Trues,BAryX),!,
                     auxLiterals:litAsgnTrues(Trues),!,
                     auxLiterals:litUnifiesWfalses(UBits,BAryX)
                 ;
                 (UMin < BMin ->
                     DD is BMin - UMin,
                     auxLists:listSplit(DD,BAryX,Trues,BAry),!,
                     auxLiterals:litAsgnTrues(Trues),!,
                     auxLiterals:litUnifiesWfalses(UBits,BAryX)
                 ;
                     auxLiterals:litUnifiesWfalses(UBits,BAry)
                 ))
             )
         ;
             (\+ var(BAry) -> % BAry -> Int
                 (var(BMin) -> BMin=0 ;
                 (integer(BMin) ; throw(model_err(int_unary2bool_array,'Min is not an integer !')))),!,
                 (BAry=[] ->
                     Int=(int,BMin,BMin,[(order,[],1)|_]),
                     ConstrsH=ConstrsT
                 ;
                     length(BAry,BLen),
                     append(_,[LBit],BAry),
                     Max is BMin + BLen,
                     Int=(int,BMin,Max,[(order,BAry,LBit)|_]),
                     bcInteger:integerType(UnaryType),
                     ConstrsH=[bc(UnaryType,Int)|ConstrsT]
                 )
             ;
                 throw(model_err(int_unary2bool_array,'int or bool_array must be defined !'))
             )
         )
   ),
   bParser:addConstraint(Head,Body).   

:- Head=int_direct2bool_array(Int,BAry,BMin,ConstrsH-ConstrsT),
   Body=(!,
         (\+ var(Int) ->  % Int -> BAry
            bcInteger:getDirectNumber(Int,(DMin,_DMax,DBits,_RDBits)),
            ConstrsH=ConstrsT,!,
            (BMin=DMin ->
                auxLiterals:litUnifiesWfalses(DBits,BAry)
            ;
                (integer(BMin) ; throw(model_err(int_direct2bool_array,'Min is not an integer !'))),!,
                    (DMin > BMin ->
                        DD is DMin - BMin,
                        auxLists:listSplit(DD,BAry,Falses,BAryX),!,
                        auxLiterals:litAsgnFalses(Falses),!,
                        auxLiterals:litUnifiesWfalses(DBits,BAryX)
                    ;
                    (DMin < BMin ->
                        DD is BMin - DMin,
                        auxLists:listSplit(DD,BAryX,Falses,BAry),!,
                        auxLiterals:litAsgnFalses(Falses),!,
                        auxLiterals:litUnifiesWfalses(DBits,BAryX)
                    ;
                        auxLiterals:litUnifiesWfalses(DBits,BAry)
                    ))
                )
            ;
            (\+ var(BAry) -> % BAry -> Int
                (var(BMin) -> BMin=0 ;
                (integer(BMin) ; throw(model_err(int_direct2bool_array,'Min is not an integer !')))),!,
                length(BAry,BLen),
                (BLen > 0 ->
                     reverse(BAry,RBAry),!,
                     Max is BMin + BLen - 1,
                     Int=(int,BMin,Max,[(direct,BAry,RBAry)|_]),
                     bcInteger:integerType(UnaryType),
                     ConstrsH=[bc(UnaryType,Int)|ConstrsT]
                ;
                     throw(model_err(int_direct2bool_array,'bool array must contain at least one element !'))
                )
            ;
                throw(model_err(int_direct2bool_array,'int or bool_array must be defined !'))
            )
        )
   ),
   bParser:addConstraint(Head,Body).    