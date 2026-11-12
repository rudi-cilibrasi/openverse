reader(t:type):=interface<computes>:
    Get()<computes>:t
box(t:type):=class<computes>(reader(t)):
    Value:t
    Get<override>()<computes>:t=Value
Make<constructor>(X:t where t:type)<computes>:=box(t):
    Value:=X
MakeInt<constructor>(X:int)<computes>:=box(int):
    Make<constructor>(X+1)
Read(X:reader(t) where t:type)<computes>:t=X.Get()
Bind(X:t where t:type)<computes>:type{_()<computes>:t}=Make(X).Get
Main():void=
    B:=Make(7)
    F:type{_()<computes>:int}=B.Get
    Print("{Read(B)} {F()} {MakeInt(9).Get()}")
    S:=Make("generic")
    G:type{_()<computes>:string}=S.Get
    Print("{Read(S)} {G()}")
    Escaped:=Bind("escaped")
    Print(Escaped())
