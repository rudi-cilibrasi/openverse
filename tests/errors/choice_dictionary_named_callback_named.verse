Fn(X:int)<computes>:int=X
ca:=class{F:type{_(:int)<computes>:int}=Fn}
cb:=class{F:type{_(:int)<computes>:int}=Fn}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{}))):A.F(?X:=1)
    Print("{Rows.Length}")
