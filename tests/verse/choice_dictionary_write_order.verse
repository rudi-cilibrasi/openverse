# Compound assignment reads its old value after the RHS, which mutates that field (the Book's order).
base:=class:
    var K:int
    Change()<transacts>:int=block{set K=100;3}
ca:=class(base){}
cb:=class(base){}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    P:=ca{K:=1}
    Q:=cb{K:=2}
    Rows:=for(A:=(Dup(P)|Dup(Q))):
        R:=set A.K+=A.Change()
        Print("{R} {A.K}")
        R
    Print("{P.K} {Q.K} {Rows.Length}")
