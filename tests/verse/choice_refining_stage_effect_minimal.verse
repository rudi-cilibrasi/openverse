pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
cell:=class{var N:int=10}
Use(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<suspends><reads>:int=
    if(Outer:=dup[P]):
        for(V:=if(D:=dup[Q])then(D.C|D.C+1)else 0):
            Sleep(0.1)
            return H.N+V
    -1
Main()<suspends>:void=
    Print("result {Use(dup(int){},dup(string){},cell{})}")
