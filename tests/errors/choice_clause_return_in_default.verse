# expect: return is not allowed in a parameter's default
pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
cell := class { var N:int=0 }
Two(N:int)<computes>:int=N|N+1
Lazy(H:cell,N:int)<transacts><decides>:int =
    N>=0
    set H.N+=1
    N|Lazy[H,N-1]
Operand(H:cell,N:int)<transacts>:int =
    set H.N+=1
    Print("operand {N} {H.N}")
    N
Wait(N:int)<suspends>:int =
    Sleep(0.1)
    N
Use(P:pair(a,b),Q:pair(c,d),?N:int=block{for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,if(A=4)then return 4 else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):Print("bad");0} where a:type,b:type,c:type,d:type):int=N
Main():void=Print("{Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"})}")
