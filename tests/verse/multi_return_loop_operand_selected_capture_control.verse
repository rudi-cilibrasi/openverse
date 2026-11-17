pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){}
F(P:pair(a,b),N:int where a:type,b:type)<computes>:b=
    if(D:=dup[P]):
        if(N>=2):return D.A|D.B
    P.B|P.B
Main():void=
    for(V:=F(dup(int){A:=3,B:=7},3)){Print("dup3 {V}")}
    for(V:=F(pair(int,int){A:=1,B:=9},3)){Print("else3 {V}")}
    for(V:=F(dup(int){A:=3,B:=7},1)){Print("dup1 {V}")}
    if(V:=F(dup(int){A:=3,B:=7},3),V=7)then Print("first {V}")else Print("bad")
    for(V:=F(dup(string){A:="a",B:="b"},3)){Print("strings {V}")}
    Print("after")
