# A void refining branch can acquire its else's string, array or logic
# type. Only an independently void else permits skipping its type probe.
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){C:int=0}
F(P:pair(a,b),N:int where a:type,b:type)<transacts>:void=
    X:=if(D:=dup[P])then Print("first")else "fallback"
    Print("string [{X}]")
    Y:=if(N=1,E:=dup[P])then Print("later")else array{1,2}
    Print("array {Y.Length}")
    Z:=if(G:=dup[P])then Print("logic")else true
    if(Z?)then Print("logic 1")else Print("logic 0")
Main()<transacts>:void=
    F(dup(int){A:=1,B:=2},1)
    F(pair(int,string){A:=1,B:="x"},1)
    F(dup(int){A:=1,B:=2},0)
