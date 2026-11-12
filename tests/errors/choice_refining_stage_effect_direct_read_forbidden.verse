# expect: do not allow
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
cell:=class{var N:int=30}
token:=class<allocates><unique>{V:int}
Reading(H:cell,N:int)<suspends><reads>:int=
    Sleep(0.01)
    H.N+N
Writing(H:cell,N:int)<suspends><writes>:int=
    Sleep(0.01)
    set H.N=N
    N
Allocating(H:cell,N:int)<suspends><allocates>:int=
    Sleep(0.01)
    T:=token{V:=N}
    T.V
Wait(N:int)<suspends><computes>:int=block{Sleep(0.01);N}
worker:=class:
    Read(H:cell,N:int)<reads>:int=H.N+N
    Write(H:cell,N:int)<suspends><writes>:int=Writing(H,N)
    ReadAlloc(H:cell,N:int)<reads><allocates>:int=
        T:=token{V:=H.N+N}
        T.V
    ReadWrite(H:cell,N:int)<reads><writes>:int=
        set H.N=H.N+N
        H.N
Make()<suspends><computes>:worker=block{Sleep(0.01);worker{}}
Use(P:pair(a,b),Q:pair(c,d),R:pair(e,f),H:cell,W:worker,F:type{_(:int)<suspends><computes>:int} where a:type,b:type,c:type,d:type,e:type,f:type)<suspends><computes>:[]int=
    if(Outer:=dup[P]):
        for(V:=if(D:=dup[Q])then(D.C|D.C+1)else 0,Z:=if(E:=dup[R])then(E.C|E.C+1)else 0):
            Reading(H,V+Z)
    else:array{}
Main()<suspends>:void=
    H:=cell{}
    R:=Use(dup(int){},dup(string){},dup(int){},H,worker{},Wait)
    Print("direct-read {R.Length} {R[0] or 0} {R[R.Length-1] or 0} {H.N}")
