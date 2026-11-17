pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){}
F(P:pair(a,b),Fallback:a where a:type,b:type)<computes>:a=
    for(I:=1..2):
        if(D:=dup[P]):return D.A
    Fallback|Fallback
Main():void=
    for(V:=F(dup(int){A:=4,B:=5},9)){Print("a {V}")}
    for(V:=F(pair(int,int){A:=4,B:=5},9)){Print("b {V}")}
