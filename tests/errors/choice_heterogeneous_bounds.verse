# expect: must be comparable
# A comparable alternative cannot strengthen the other alternative's bound.
box:=class{}
Dup(X:t where t:type)<computes>:t=X|X
Equal(X:t,Y:t where t:subtype(comparable))<computes>:int=if(X=Y)then 1 else 0
Main():void=
    Rows:=for(A:=(Dup(1)|Dup(box{})),B:=(Dup(1)|Dup("s"))):Equal(A,A)
    Print("{Rows.Length}")
