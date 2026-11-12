# A method instance supplied by a later generator keeps the original fallback.
Dup(X:t where t:type)<computes>:t=X|X
foo(t:type):=class<computes>{V:t}
bar(t:type):=class<computes>{V:t}
ca:=class{M(X:u where u:type)<computes>:foo(u)=foo(u){V:=X}}
cb:=class{M(X:u where u:type)<computes>:bar(u)=bar(u){V:=X}}
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),X:=(1|"value")):
        B:=A.M(X)
        array{B.V}.Length
    Print("{Rows.Length}")
