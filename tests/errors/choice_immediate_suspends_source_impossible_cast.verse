# expect: would always fail
Two(N:int):int=N|N+1
pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) {}
Main()<suspends>:void =
    P:=pair(int,string){A:=1,B:="s"}
    for(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2))):
        if(D:=dup[P])then Print("bad")else Print("accepted")
