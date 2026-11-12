# Preserve tuple equations, comparable witnesses, defaults and result fields.
box(t:type):=class{V:t;K:int}
Dup(X:t where t:type)<computes>:t=X|X
Equal(X:t,Y:t where t:subtype(comparable))<computes>:int=if(X=Y)then 1 else 0
Keep(X:t,?Y:t=X,?Empty:[]t=Concatenate() where t:subtype(comparable))<computes>:int=
    Equal(X,Y)+Empty.Length
Select(X:int)<computes>:int=100+X
Select(X:string)<computes>:int=200+X.Length
Main():void=
    var Total:int=0
    Rows:=for(A:=(Dup(1)|Dup("x")),B:=(Dup((1,1))|Dup(("s","s"))),C:=(Dup(box(int){V:=1,K:=2})|Dup(box(string){V:="s",K:=3}))):
        set Total+=Keep(A)+Equal(B(0),B(1))+C.K
        (A,B,C.K)
    var Sum:int=0
    for(Row:Rows):set Sum+=Row(2)
    Print("{Rows.Length} {Total} {Sum}")
    # An overload must see the original static type of each alternative.
    Scores:=for(A:=(Dup(1)|Dup("x")),B:=(Dup(7)|Dup("y"))):Select(A)+Keep(B)
    var Selected:int=0
    for(Score:Scores):set Selected+=Score
    Print("{Scores.Length} {Selected}")
