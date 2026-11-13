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
runner(t:type):=class:
    Value:t
    Echo(X:e where e:type):e=X
    Run(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:[]t =
        var Total:int=0
        R:=for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
            Sleep(0.01)
            set Total+=1
            Echo(Value)
        Print("class count {Total}")
        R
Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends>:void =
    R:=runner(int){Value:=7}.Run(P,Q)
    for(V:R):Print("class value {V}")
    S:=runner(string){Value:="x"}.Run(P,Q)
    for(V:S):Print("class value {V}")
Main()<suspends>:void=Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})
