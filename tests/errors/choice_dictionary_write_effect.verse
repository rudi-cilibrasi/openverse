# expect: effect <writes>
ca:=class{var K:int=1}
cb:=class{var K:int=2}
Dup(X:t where t:type)<computes>:t=X|X
Observe(P:ca,Q:cb)<reads>:int=
    Rows:=for(A:=(Dup(P)|Dup(Q))):set A.K=3
    Rows.Length
Main():void=Print("{Observe(ca{},cb{})}")
