pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Child(Label:string,N:int)<suspends><computes>:void=
    Print("{Label} {N}")
    Sleep(0.0)
Pure(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<computes>:void=
    for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0,W:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
        T:=spawn{Child("computes",V+W)}
Read(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<reads>:void=
    for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0,W:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
        T:=spawn{Child("reads",V+W)}
Allocate(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<allocates>:void=
    for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0,W:=if(E:=dup[Q])then(E.C|E.C+1)else 0):
        T:=spawn{Child("allocates",V+W)}
Main()<suspends>:void=
    Pure(dup(int){},dup(string){})
    Read(dup(int){},dup(string){})
    Allocate(dup(int){},dup(string){})
    Sleep(1.0)
