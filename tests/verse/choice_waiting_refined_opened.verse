pair(a:type,b:type) := class { A:a; B:b }
loose(a:type,b:type) := class(pair(a,b)) { C:int=4 }
dup(t:type) := class(loose(t,t)) {}
cell := class { var N:int=0 }
Lazy(N:int)<computes><decides>:int =
    N>=0
    N|Lazy[N-1]
Wait(N:int)<suspends>:int =
    Sleep(0.01)
    N
expr(t:type):=class{}
pairE(a:type,b:type):=class(expr(tuple(a,b))){L:a;R:b}
Use(E:expr(t),Fallback:t,Q:pair(c,d),Hit:logic where t:type,c:type,d:type)<suspends>:[]t =
    for(V:t=if(D:=pairE[E])then((D.L,D.R)|(D.L,D.R))else Fallback,
        W:=if(F:=dup[Q])then(F.C|F.C+1)else 0):
        Sleep(0.01)
        Empty:[]t=array{}
        Print("opened {W}")
        V
Main()<suspends>:void =
    R:=Use(pairE(int,string){L:=7,R:="x"},(7,"x"),dup(int){A:=1,B:=2},true)
    for(V:R):Print("value {V(0)} {V(1)}")
    S:=Use(expr(int){},99,dup(string){A:="s",B:="t"},false)
    for(V:S):Print("value {V}")
