pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){}
cell:=class{var N:int=10}
token:=class<allocates><unique>{V:int}
Two(N:int)<computes>:int=N|N+1
Early(N:int)<computes>:int=
    if(N<0):return N
    N|N+1
Reading(H:cell,N:int)<suspends><reads>:int=
    Sleep(0.0)
    H.N+N
Writing(H:cell,N:int)<suspends><writes>:int=
    Sleep(0.0)
    set H.N=N
    N
Allocating(H:cell,N:int)<suspends><allocates>:int=
    Sleep(0.0)
    T:=token{V:=N}
    T.V
waiter:=class:
    Read(H:cell,N:int)<suspends><reads>:int=Reading(H,N)
    Write(H:cell,N:int)<suspends><writes>:int=Writing(H,N)
    Allocate(H:cell,N:int)<suspends><allocates>:int=Allocating(H,N)
Composed(P:pair(a,b),H:cell,W:waiter,F:type{_(:cell,:int)<suspends><allocates>:int} where a:type,b:type)<suspends><allocates>:int=
    if(Outer:=dup[P]):
        Sleep(0.0)
        for(A:=(Two(1)|Two(3)),A=1,B:=(Two(10)|Two(20)),B=10):
            return Allocating(H,A+B)
    -1
Exclusive(P:pair(a,b),H:cell,W:waiter,F:type{_(:cell,:int)<suspends><allocates>:int} where a:type,b:type)<suspends><allocates>:int=
    if(Outer:=dup[P]):
        Sleep(0.0)
        for(A:=Early(1),A=1,B:=Early(10),B=10):
            return W.Allocate(H,A+B)
    -1
Nested(P:pair(a,b),H:cell,W:waiter,F:type{_(:cell,:int)<suspends><allocates>:int} where a:type,b:type)<suspends><allocates>:int=
    if(Outer:=dup[P]):
        Sleep(0.0)
        Rows:=for(A:=(Two(1)|Two(3)),A=1,B:=Early(10),B=10):
            for(C:=(Two(20)|Two(22)),C=20,D:=Early(30),D=30):
                F(H,A+B+C+D)
        for(Row:Rows,V:Row):return V
    -1
Main()<suspends>:void=
    block:
        H:=cell{}
        V:=Composed(dup(int){},H,waiter{},Allocating)
        Print("composed allocates {V} {H.N}")
    block:
        H:=cell{}
        V:=Exclusive(dup(int){},H,waiter{},Allocating)
        Print("exclusive allocates {V} {H.N}")
    block:
        H:=cell{}
        V:=Nested(dup(int){},H,waiter{},Allocating)
        Print("nested-fn allocates {V} {H.N}")
