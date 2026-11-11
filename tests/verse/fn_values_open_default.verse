Id(X:t where t:type):t=X
holder(t:type):=class:
    V:t
    F:type{_(:t):t}=Id
    Go():t=F(V)
Make(X:t where t:type):holder(t)=holder(t){V:=X}
Main():void=
    B:=Make(8)
    S:=Make("word")
    Print("{B.Go()} {S.Go()}")
