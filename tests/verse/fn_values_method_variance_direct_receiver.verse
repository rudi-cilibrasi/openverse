box(t:type):=class:
    V:t
    Get():t=V
    Pair(X:u where u:type):tuple(t,u)=(V,X)
Main():void=
    B:=box(int){V:=7}
    R:rational=B.Get()
    P:tuple(int,string)=B.Pair("value")
    Print("{Floor(R)} {P(0)} {P(1)}")
