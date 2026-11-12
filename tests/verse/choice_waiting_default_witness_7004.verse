pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
root:=class{}
extra(t:type):=class(root){X:t;C:int=4}
cell:=class{var N:int=0}
Id(X:t where t:type)<computes>:t=X
Values(P:pair(a,b) where a:type,b:type):[]int=for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):V
Opened(P:root):[]int=for(V:=if(D:=extra[P])then(D.C+Id(array{D.X}).Length|D.C+Id(array{D.X}).Length+1)else 0):V
Lazy(N:int)<computes><decides>:int=block{N>=0;N|Lazy[N-1]}
Global:root=root{}
holder:=interface{Run(P:pair(a,b),H:cell,?N:int=0 where a:type,b:type)<suspends>:int}
box(t:type):=class(holder):
    X:t
    Run<override>(P:pair(a,b),H:cell,?N:int=block{branch{defer:Print("background {H.N}");Sleep(0.05);set H.N=10;Sleep(1.0)};R:=for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0,L:=Lazy[V]):block{defer:Print("body {H.N}");Sleep(0.1);E:[]a=Concatenate();set H.N+=V+L+E.Length;V+L};R.Length} where a:type,b:type)<suspends>:int=N
Make():box(string)=box(string){X:="tag"}
B:holder=Make()
Use(P:pair(a,b),H:cell where a:type,b:type)<suspends>:int=
    defer:Print("source {H.N}")
    R:=B.Run(P,H)
    Print("after {H.N}")
    R
Main()<suspends>:void=
    H:=cell{}
    R:=Use(pair(int,string){},H)
    Print("result {R} state {H.N}")
