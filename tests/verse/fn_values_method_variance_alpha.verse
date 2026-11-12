box(a:type,b:type):=class:
    A:a
    B:b
    Code()<computes>:int=7
First(B:box(t,u) where t:type,u:type)<computes>:type{_()<computes>:rational}=B.Code
Second(B:box(v,w) where v:type,w:type)<computes>:type{_()<computes>:rational}=B.Code
Main():void=
    B:=box(int,string){A:=3,B:="s"}
    F:=First(B)
    G:=Second(B)
    Print("{Floor(F())} {Floor(G())}")
