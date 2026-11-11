# expect: break is only allowed inside loop
pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
cell := class { var N:int=0 }
Two(N:int)<computes>:int=N|N+1
Lazy(H:cell,N:int)<transacts><decides>:int =
    N>=0
    set H.N+=1
    N|Lazy[H,N-1]
Use(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends>:int =
    loop:
        if(F:=dup[P]):
            for(A:array{4,5}):
                for(B:array{4,5},if(B=4)then break else 0,C:=Two(8)):Print("bad")
            break
        break
    99
Main()<suspends>:void =
    H:=cell{}
    Print("result {Use(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},H)} {H.N}")
