# Read the callback before an argument replaces the mutable field.
cell:=class{var N:int=0}
ReadFirst(H:cell,X:int)<reads>:int=1
ReadNext(H:cell,X:int)<reads>:int=10
WriteFirst(H:cell,X:int)<transacts>:int=block{set H.N+=1;2}
WriteNext(H:cell,X:int)<transacts>:int=block{set H.N+=2;20}
ca:=class:
    var F:type{_(:cell,:int)<reads>:int}=ReadFirst
    Swap()<transacts>:int=block{set F=ReadNext;1}
cb:=class:
    var F:type{_(:cell,:int)<transacts>:int}=WriteFirst
    Swap()<transacts>:int=block{set F=WriteNext;2}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    H:=cell{}
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),B:=(Dup(1)|Dup("s"))):A.F(H,A.Swap())
    var Sum:int=0
    for(Row:Rows):set Sum+=Row
    Print("{Rows.Length} {Sum} {H.N}")
