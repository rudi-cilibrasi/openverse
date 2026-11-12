ca:=class:
    M(X:t,?Y:t=X where t:type)<computes>:t=Y
cb:=class:
    M(X:t,?Y:t=X where t:type)<computes>:t=Y
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{}))):A.M(7)
    Print("{Rows.Length}")
    for(V:Rows):Print("{V}")
