# Getters observe the current object after an effectful method call.
ca:=class:
    var K:int
    Tick(Delta:int)<transacts>:ca=
        set K+=Delta
        Print("a {K}")
        Self
cb:=class:
    var K:int
    Tick(Delta:int)<transacts>:cb=
        set K+=Delta
        Print("b {K}")
        Self
Dup(X:t where t:type)<computes>:t=X|X
Keep(X:t where t:subtype(comparable))<computes>:int=if(X=X)then 1 else 0
Main():void=
    P:=ca{K:=1}
    Q:=cb{K:=2}
    Rows:=for(A:=(Dup(P)|Dup(Q)),B:=(Dup(1)|Dup("s"))):
        Before:=A.K
        After:=A.Tick(1).K
        Current:=A.K
        100*Before+10*After+if(Current=After)then Keep(B) else 0
    var Sum:int=0
    for(Row:Rows):set Sum+=Row
    Print("{Rows.Length} {Sum} {P.K} {Q.K}")
