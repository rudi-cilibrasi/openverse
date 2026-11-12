# Both RHS alternatives use the value saved before that choice.
ca:=class{var K:int=1}
cb:=class{var K:int=2}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    P:=ca{}
    Q:=cb{}
    Rows:=for(A:=(Dup(P)|Dup(Q)),R:=set A.K+=(1|2)):
        Print("{R} {A.K}")
        R
    var Total:int=0
    for(Row:Rows):set Total+=Row
    Print("{P.K} {Q.K} {Rows.Length} {Total}")
