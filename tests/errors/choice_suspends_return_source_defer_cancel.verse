# expect: Cancel suspends, and a defer cannot suspend
pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }

counter := class { var N:int=0 }
Worker(C:counter)<suspends>:void =
    defer:Print("worker {C.N}")
    Sleep(2.0)
Use(P:pair(a,b),Q:pair(c,d),C:counter,T:task(void) where a:type,b:type,c:type,d:type)<suspends>:int =
    var Total:int=0
    defer:
        Print("source {Total}")
        set C.N=Total
        T.Cancel()
    for(A:=(4|5),B:=(4|5)):
        set Total+=A+B
        if(B=5)then return Total
    -1
Main()<suspends>:void =
    C:=counter{}
    T:=spawn{Worker(C)}
    Print("result {Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},C,T)}")
