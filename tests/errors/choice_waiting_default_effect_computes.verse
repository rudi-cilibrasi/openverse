# expect: do not allow
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){}
cell:=class{var N:int=0}
Write(H:cell,N:int)<writes>:int=block{set H.N=N;N}
Two(N:int)<computes>:int=N|N+1
base(t:type):=class:
    Go(H:cell,X:t,?N:int=0)<suspends><computes>:int=0
impl:=class(base(int)):
    Go<override>(H:cell,X:int,?N:int=Write(H,X))<suspends><computes>:int=block{Sleep(0.0);N}
Use(P:pair(a,b),W:base(u),X:u,H:cell where a:type,b:type,u:type)<suspends><computes>:int=
    if(D:=dup[P]):
        Sleep(0.0)
        for(A:=(Two(1)|Two(3)),B:=(Two(4)|Two(6))):return W.Go(H,X)
    -1
Main()<suspends>:void=
    H:=cell{}
    N:=Use(dup(int){},impl{},8,H)
    Print("result {N} state {H.N}")
