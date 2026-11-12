# expect: effect <reads>
cell:=class{var N:int=3}
ca:=class{var K:int=1}
cb:=class{var K:rational=1}
Dup(X:t where t:type)<computes>:t=X|X
Peek(H:cell)<reads>:int=H.N
Observe(P:ca,Q:cb,H:cell)<writes>:int=
    Rows:=for(A:=(Dup(P)|Dup(Q))):set A.K=Peek(H)
    Rows.Length
Main():void=Print("{Observe(ca{},cb{},cell{})}")
