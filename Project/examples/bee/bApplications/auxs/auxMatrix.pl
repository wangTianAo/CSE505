% usefull functions on Matrix
% Author: Amit Metodi
% Last Updated: 28/07/2010

:- module('auxMatrix',
          [matrixCreate/3,matrixSize/3,
           matrixGetSubMtrx0/6,
           matrixTranspose/2,
           matrixMultiply/3,
           matrixGetRow/3,  matrixGetCol/3,  matrixGetCell/4,
           matrixGetRow0/3, matrixGetCol0/3, matrixGetCell0/4,
           matrixPrint/1, matrixSave2File/2, matrixSave2File_nospc/2,
           matrixEqualRows/3,
           matrix2vector/2]).

% matrixCreate(height+,width+, matrix-)
matrixCreate(0,_,[]):-!.
matrixCreate(Y,XsLen,[Xs|MYs]):-!,
   length(Xs,XsLen),
   Y1 is Y-1,
   matrixCreate(Y1,XsLen,MYs).


matrixSize(Mtrx,Rows,Cols):-
   length(Mtrx,Rows),
   (Rows > 0 ->
         [R|_]=Mtrx,
         length(R,Cols)
         ;
         Cols=0).

% matrixGetRow(matrix+,rowID+, row-)
% rowID starts with 1
matrixGetRow(Matrix, RowId, Row):-
   nth1(RowId,Matrix,Row).


% matrixGetCol(matrix+,colID+, col-)
% colID starts with 1
matrixGetCol([], _, []).
matrixGetCol([Row|Matrix], ColId, [X|Xs]):-
   nth1(ColId,Row,X),
   matrixGetCol(Matrix, ColId, Xs).

% matrixGetCell(matrix+,x+,y+, cell-)
% x,y starts with 1
matrixGetCell(Matrix,X,Y,Cell):-
   nth1(Y,Matrix,Row),
   nth1(X,Row,Cell).



% matrixGetRow0(matrix+,rowID+, row-)
% rowID starts with 0
matrixGetRow0(Matrix, RowId, Row):-
   nth0(RowId,Matrix,Row).


% matrixGetCol0(matrix+,colID+, row-)
% colID starts with 0
matrixGetCol0([], _, []).
matrixGetCol0([Row|Matrix], ColId, [X|Xs]):-
   nth0(ColId,Row,X),
   matrixGetCol0(Matrix, ColId, Xs).


% matrixGetCell0(matrix+,x+,y+, cell-)
% x,y starts with 0
matrixGetCell0(Matrix,X,Y,Cell):-
   nth0(Y,Matrix,Row),
   nth0(X,Row,Cell).
   
   

matrixGetSubMtrx0(Mtrx,StartX,StartY,XLen,YLen, NewMtrx):-
   length(DropRows,StartY),
   length(KeepRows,YLen),
   append([DropRows,KeepRows,_],Mtrx),
   matrixGetSubMtrx0_rows(KeepRows,StartX,XLen,NewMtrx).
   
matrixGetSubMtrx0_rows([],_,_,[]).
matrixGetSubMtrx0_rows([RowI|KeepRows],StartX,XLen,[KeepCells|NewMtrx]):-
   length(DropCells,StartX),
   length(KeepCells,XLen),
   append([DropCells,KeepCells,_],RowI),
   matrixGetSubMtrx0_rows(KeepRows,StartX,XLen,NewMtrx).

   
   
% matrixPrint(matrix+)
matrixPrint([]).
matrixPrint([Line|Matrix]):-
    matrixPrintLine(Line),
    matrixPrint(Matrix).
matrixPrintLine([]):-writeln(' ').
matrixPrintLine([X|Xs]):-write(X),write(' '),matrixPrintLine(Xs).

matrixPrint2([]).
matrixPrint2([Line|Matrix]):-
    matrixPrintLine2(Line),
    matrixPrint2(Matrix).
matrixPrintLine2([]):-writeln(' ').
matrixPrintLine2([X|Xs]):-(var(X) -> write(' ?  ') ; writef('%4c',[X])),matrixPrintLine2(Xs).

    
% matrixEqualRows(matrix+,Seq+,Cnt-)
% count how many rows equals to sequance
matrixEqualRows([],_,0).
matrixEqualRows([Row|Rows],Seq,Cnt):-
    matrixEqualRows(Rows,Seq,Cnt2),!,
    (Row==Seq ->
        Cnt is Cnt2 + 1 ;
        Cnt = Cnt2).
        
% matrixTranspose_null(Mtrx,MtrxTr)
matrixTranspose(Rows,[]) :-
        matrixTranspose_null(Rows).
matrixTranspose(Rows,[FirstCol|Cols]) :-
        matrixTranspose_row(Rows,FirstCol,RestRows),
        matrixTranspose(RestRows,Cols).

matrixTranspose_row([],[],[]).
matrixTranspose_row([[X|RestRow]|Rows],[X|Col],[RestRow|RestRows]) :-
        matrixTranspose_row(Rows,Col,RestRows).

matrixTranspose_null([]).
matrixTranspose_null([[]|Ns]) :-
        matrixTranspose_null(Ns).

%matrixMultiply(Mtrx1+,Mtrx2+,MtrxRes-)
matrixMultiply(Mtrx1,Mtrx2,MtrxRes):-
    matrixSize(Mtrx1,Rows,TMP),
    matrixSize(Mtrx2,TMP,Cols),
    matrixCreate(Rows,Cols,MtrxRes),
    matrixMul(Rows,Cols,Cols,Mtrx1,Mtrx2,MtrxRes).
    
    
matrixMul_cell([],[],0).
matrixMul_cell([R|Row],[C|Col],Cell):-
    matrixMul_cell(Row,Col,CellTmp),
    Cell is R * C + CellTmp.

matrixMul_cell(Mtrx1,Mtrx2,MtrxRes,RowID,ColID):-
    matrixGetRow(Mtrx1, RowID, Row),
    matrixGetCol(Mtrx2, ColID, Col),
    matrixGetCell(MtrxRes, RowID, ColID, Cell),
    matrixMul_cell(Row,Col,Cell).

matrixMul(0,_,_,_,_,_):-!.
matrixMul(RowsCnt,0,ColsCntOrg,Mtrx1,Mtrx2,MtrxRes):-!,
    RowsCnt1 is RowsCnt-1,
    matrixMul(RowsCnt1,ColsCntOrg,ColsCntOrg,Mtrx1,Mtrx2,MtrxRes).
matrixMul(RowsCnt,ColsCnt,ColsCntOrg,Mtrx1,Mtrx2,MtrxRes):-
    matrixMul_cell(Mtrx1,Mtrx2,MtrxRes,RowsCnt,ColsCnt),
    ColsCnt1 is ColsCnt-1,
    matrixMul(RowsCnt,ColsCnt1,ColsCntOrg,Mtrx1,Mtrx2,MtrxRes).
    
    
matrixSave2File(Mtrx,Filename):-
    open(Filename, write, Stream),!,
    matrixSave2File_stream(Mtrx,Stream),!,
    close(Stream).
matrixSave2File_stream([],_).
matrixSave2File_stream([Line|Matrix],Stream):-
    matrixSave2File_streamLine(Line,Stream),!,
    matrixSave2File_stream(Matrix,Stream).
matrixSave2File_streamLine([X|Xs],Stream):-
    write(Stream, X), write(Stream, ' '),!,
    matrixSave2File_streamLine(Xs,Stream).
matrixSave2File_streamLine([],Stream):-
    nl(Stream).



matrixSave2File_nospc(Mtrx,Filename):-
    open(Filename, write, Stream),!,
    matrixSave2File_stream_nospc(Mtrx,Stream),!,
    close(Stream).
matrixSave2File_stream_nospc([],_).
matrixSave2File_stream_nospc([Line|Matrix],Stream):-
    matrixSave2File_streamLine_nospc(Line,Stream),!,
    matrixSave2File_stream_nospc(Matrix,Stream).
matrixSave2File_streamLine_nospc([X|Xs],Stream):-
    write(Stream, X),!,
    matrixSave2File_streamLine_nospc(Xs,Stream).
matrixSave2File_streamLine_nospc([],Stream):-
    nl(Stream).


matrix2vector(Mtrx,Vec):-
    append(Mtrx,Vec).

