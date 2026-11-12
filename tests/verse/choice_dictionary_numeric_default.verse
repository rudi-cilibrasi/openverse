ca:=class{var K:int=1}
cb:=class{var K:rational=1/1}
Dup(X:t where t:type)<computes>:t=X|X
Echo(?X:t=3 where t:type)<computes>:t=X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{}))):
        R:=set A.K=Echo()
        0
    Print("{Rows.Length}")
