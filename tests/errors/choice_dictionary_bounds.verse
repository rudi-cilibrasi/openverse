# expect: must be comparable
# A result equation cannot strengthen a non-comparable receiver alternative.
ca:=class<unique>:
    Me()<computes>:ca=Self
cb:=class:
    Me()<computes>:cb=Self
Dup(X:t where t:type)<computes>:t=X|X
Equal(X:t,Y:t where t:subtype(comparable))<computes>:int=if(X=Y)then 1 else 0
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),B:=(Dup(1)|Dup("s"))):Equal(A.Me(),A.Me())
    Print("{Rows.Length}")
