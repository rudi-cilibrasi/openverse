# expect: not a var
ca:=class{var K:int=1}
cb:=class{K:int=2}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{}))):set A.K=3
    Print("{Rows.Length}")
