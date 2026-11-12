Integer(X:int)<computes>:int=1
String(X:string)<computes>:int=2
ca:=class{V:int;F:type{_(:int)<computes>:int}}
cb:=class{V:string;F:type{_(:string)<computes>:int}}
Dup(X:t where t:type)<computes>:t=X|X
Keep(X:t where t:subtype(comparable))<computes>:int=if(X=X)then 1 else 0
Main():void=
    Rows:=for(A:=(Dup(ca{V:=3,F:=Integer})|Dup(cb{V:="s",F:=String})),B:=(Dup(1)|Dup("s"))):A.F(A.V)+Keep(B)
    var Sum:int=0
    for(Row:Rows):set Sum+=Row
    Print("{Rows.Length} {Sum}")
