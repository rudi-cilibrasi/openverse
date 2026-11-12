# expect: effect <reads>
# A mutable field read retains its source admission requirement.
ca:=class{var K:int=1}
cb:=class{var K:int=2}
Dup(X:t where t:type)<computes>:t=X|X
Observe(P:ca,Q:cb)<computes>:int=
    Rows:=for(A:=(Dup(P)|Dup(Q)),B:=(Dup(1)|Dup("s"))):A.K
    Rows.Length
Main():void=Print("{Observe(ca{},cb{})}")
