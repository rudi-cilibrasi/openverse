pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
cell:=class{var N:int=0}
token:=class<unique>{V:int}
Use(P:pair(a,b),Q:pair(c,d),S:pair(e,f),H:cell,B:int where a:type,b:type,c:type,d:type,e:type,f:type)<suspends><reads><writes>:int=
    if(Outer0:=dup[P]):
        if(Outer1:=dup[Q]):
            for(V:=if(D:=dup[S])then(D.C|D.C+1)else 0):
                defer:Print("cleanup {V}")
                Print("start {V}")
                Sleep(0.1)
                Out:=H.N+V
                set H.N=Out
                Print("done {V} {Out}")
    0
Main()<suspends>:void=
    H:=cell{N:=10}
    T:=spawn{Use(dup(int){},dup(string){},dup(char){},H,10)}
    Print("created {H.N}")
    R:=T.Await()
    Print("result {R} {H.N}")
