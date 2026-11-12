# Differing subclass layouts use the same instantiated base-field contract.
base:=class{K:int}
ca:=class(base){A:string="a"}
cb:=class(base){B:int=7;C:string="c"}
Dup(X:t where t:type)<computes>:t=X|X
Keep(X:t,?Y:t=X where t:subtype(comparable))<computes>:int=if(X=Y)then 1 else 0
Main():void=
    Rows:=for(A:=(Dup(ca{K:=1})|Dup(cb{K:=2})),B:=(Dup(1)|Dup("x"))):A.K+Keep(B)
    var Sum:int=0
    for(Row:Rows):set Sum+=Row
    Print("{Rows.Length} {Sum}")
    if(A:=(Dup(ca{K:=1})|Dup(cb{K:=2})),B:=(Dup(1)|Dup("x")),A.K=2,Keep(B)=1):
        Print("first {A.K}")
