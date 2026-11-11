pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){C:int=4}
cell:=class{var N:int=10}
listener:=class:
    var Sum:int=0
    Add(N:int):void=
        set Sum+=N
        Print("heard {N} {Sum}")
worker:=class:
    Signal(H:cell,N:int)<reads>:int=H.N+N
Make()<suspends><computes>:worker=block{Sleep(0.1);worker{}}
Wait(N:int)<suspends><computes>:int=block{Sleep(0.1);N}
Use(P:pair(a,b),Q:pair(c,d),H:cell,W:worker,F:type{_(:int)<suspends><computes>:int} where a:type,b:type,c:type,d:type)<suspends><reads>:int=
    if(Outer:=dup[P]):
        for(V:=if(D:=dup[Q])then(D.C|D.C+1)else 0):
            defer:Print("body")
            return (Make()).Signal(H,V)
    -1
Main()<suspends>:void=
    H:=cell{}
    R:=Use(dup(int){A:=1,B:=2},dup(string){A:="a",B:="b"},H,worker{},Wait)
    Print("result {R} {H.N}")
