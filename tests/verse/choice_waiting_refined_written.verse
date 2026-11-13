pair(a:type,b:type):=class{}
loose(a:type,b:type):=class(pair(a,b)){}
dup(t:type):=class(loose(t,t)){}
Use(P:pair(a,b),Q:pair(c,d),Witness:z where a:type,b:type,c:type,d:type,z:type)<suspends><computes>:void =
    for(A:=if(D:=dup[P])then(1|2)else 0,B:=if(E:=dup[Q])then(3|4)else 0):
        Sleep(0.01)
        Empty:[]z=array{}
        Print("witness {A} {B} {Empty.Length}")
Main()<suspends>:void=Use(dup(int){},dup(string){},"w")
