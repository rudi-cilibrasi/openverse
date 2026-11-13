pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
cell := class { var N:int=10 }
token := class<allocates><unique>:
    V:int
    block:Print("alloc {V}")
Two(N:int)<computes>:int=N|N+1
Lazy(N:int)<computes><decides>:int =
    N>=0
    N|Lazy[N-1]
Read(H:cell,N:int)<reads>:int=H.N+N
Write(H:cell,N:int)<writes>:int =
    set H.N=N
    N
Allocate(H:cell,N:int)<allocates>:int =
    T:=token{V:=N}
    T.V
Use0(P:pair(a,b),Q:pair(c,d),R:pair(e,f),H:cell where a:type,b:type,c:type,d:type,e:type,f:type)<suspends><writes>:int =
    if(F:=dup[P]):
        if(G:=dup[Q]):
            Sleep(0.01)
            for(A:=if(D:=dup[R])then(D.C|D.C+1)else 0,B:=if(E:=dup[P])then(E.C|E.C+1)else 0):return Write(H,A+B)
    -1

Use1(P:pair(a,b),Q:pair(c,d),R:pair(e,f),H:cell where a:type,b:type,c:type,d:type,e:type,f:type)<suspends><allocates>:int =
    if(F:=dup[P]):
        Sleep(0.01)
        for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0,L:=Lazy[2]):return Allocate(H,A+B+L)
    -1

Use2(P:pair(a,b),Q:pair(c,d),R:pair(e,f),H:cell where a:type,b:type,c:type,d:type,e:type,f:type)<suspends><writes>:int =
    if(F:=dup[P]):
        Sleep(0.01)
        if(Z:=(option{
            Rows:=for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0,B:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
                Print("discard {Write(H,A+B)}")
                false?
                A
            Rows.Length
        })?):Print("bad {Z}")
    -1
Main()<suspends>:void =
    H0:=cell{}
    Print("result {Use0(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},dup(char){A:='a',B:='b'},H0)} {H0.N}")
    H1:=cell{}
    Print("result {Use1(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},dup(char){A:='a',B:='b'},H1)} {H1.N}")
    H2:=cell{}
    Print("result {Use2(dup(int){A:=1,B:=2},dup(string){A:="s",B:="t"},dup(char){A:='a',B:='b'},H2)} {H2.N}")
