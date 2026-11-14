pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
root:=class{}
extra(t:type):=class(root){X:t;C:int=4}
cell:=class{var N:int=0}
Values(P:pair(a,b) where a:type,b:type):[]int=for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):V
Lazy(N:int)<computes><decides>:int=block{N>=0;N|Lazy[N-1]}
holder:=interface<computes>{Run(P:pair(a,b),H:cell,?N:int=0 where a:type,b:type)<suspends>:int}
box(t:type):=class<computes>(holder):
    X:t
    Run<override>(P:pair(a,b),H:cell,?N:int=block{R:=for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):block{defer:Print("body {H.N}");Sleep(0.1);set H.N+=V;V};R.Length} where a:type,b:type)<suspends>:int=N
Make()<computes>:box(string)=box(string){X:="tag"}

B:holder=Make()
Use(P:pair(a,b),H:cell where a:type,b:type)<suspends>:int=
    defer:Print("source {H.N}")
    B.Run(P,H)
Main()<suspends>:void=
    H:=cell{}
    R:=race:
        Use(dup(int){},H)
        block{Sleep(0.15);-1}
    Print("result {R} state {H.N}")
