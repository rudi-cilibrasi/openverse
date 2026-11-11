# expect: effect <writes>
pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) {}
base(t:type) := class:
    F(X:t,?D:int=0)<computes>:int=D
ib := class(base(int)):
    var Calls:int=0
    F<override>(X:int,?D:int=block{set Calls+=1;X})<computes>:int=D
Run(P:pair(a,b),Q:base(c),X:c where a:type,b:type,c:type)<computes>:int=
    if(D:=dup[P]):
        for(A:=0|1):
            return Q.F(X)
    -1
RunWaiting(P:pair(a,b),Q:base(c),X:c where a:type,b:type,c:type)<suspends><transacts>:int=
    var Total:int=1
    defer:Print("source {Total}")
    if(D:=dup[P]):
        Sleep(0.0)
        for(A:=0|1):
            set Total+=Q.F(X)
            return Total
    -1
Main()<suspends><transacts>:void=
    C:=ib{}
    Print("sync {Run(dup(int){A:=1,B:=2},C,7)} {C.Calls}")
    Print("async {RunWaiting(dup(int){A:=1,B:=2},C,7)} {C.Calls}")
