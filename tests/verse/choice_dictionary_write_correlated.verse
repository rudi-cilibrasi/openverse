# The assigned value and the field retain the same precise comparable type.
ca:=class{var K:int=7}
cb:=class{var K:string="s"}
Dup(X:t where t:type)<computes>:t=X|X
Keep(X:t where t:type)<computes>:t=X
Equal(X:t,Y:t where t:subtype(comparable))<computes>:int=if(X=Y)then 1 else 0
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{}))):
        Saved:=set A.K=Keep(A.K)
        Equal(Saved,A.K)
    var Total:int=0
    for(Row:Rows):set Total+=Row
    Print("{Total}")
