pair(a:type,b:type):=class{}
loose(a:type,b:type):=class(pair(a,b)){}
dup(t:type):=class(loose(t,t)){}
Use(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<suspends><computes>:void =
    var Total:int=7
    branch:
        Sleep(0.1)
        set Total+=100
        Print("observe {Total}")
    for(A:=if(D:=dup[P])then(1|2)else 0,B:=if(E:=dup[Q])then(3|4)else 0):
        Sleep(0.2)
        Print("readonly {A} {B} {Total}")
    Print("done {Total}")
Main()<suspends>:void=Use(dup(int){},dup(string){})
