# expect: the for's values have the type
# Multiple incomparable common interfaces must remain an ambiguous join.
i1:=interface{}
i2:=interface{}
a:=class(i1,i2){}
b:=class(i1,i2){}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(a{})|Dup(b{})),B:=(Dup(1)|Dup("s"))):A
    Print("{Rows.Length}")
