pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
cell:=class{var N:int=10}
token:=class<unique>{V:int}
Read(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends><reads>:int=
    if(Outer:=dup[P]):
        for(V:=if(D:=dup[Q])then(D.C|D.C+1)else 0):
            Sleep(0.1)
            return H.N+V
    -1
Write(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends><writes>:int=
    if(Outer:=dup[P]):
        for(V:=if(D:=dup[Q])then(D.C|D.C+1)else 0):
            Sleep(0.1)
            set H.N=V
            return V
    -1
Allocate(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends><allocates>:int=
    if(Outer:=dup[P]):
        for(V:=if(D:=dup[Q])then(D.C|D.C+1)else 0):
            Sleep(0.1)
            T:=token{V:=V}
            return T.V
    -1
Main()<suspends>:void=
    H:=cell{}
    Print("read {Read(dup(int){},dup(string){},H)}")
    Print("fallback {Read(dup(string){},pair(int,string){},H)}")
    Print("outer {Read(pair(int,string){},dup(int){},H)}")
    Print("write {Write(dup(int){},dup(string){},H)}")
    Print("allocate {Allocate(dup(string){},dup(int){},H)}")
    Print("state {H.N}")
