pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){}
Bounds()<computes>:int=1|2
Pick(P:pair(a,b),Other:b,Fallback:a where a:type,b:subtype(comparable))<transacts>:a=
    var Saved:b=Other
    defer:
        if(Saved=Other)then Print("outer old")else Print("outer new")
    for(I:=Bounds()..2):
        if(D:=dup[P],I=2):
            defer:set Saved=D.B
            return Saved|Saved
    Fallback|Fallback
Main()<transacts>:void=
    for(V:=Pick(dup(int){A:=4,B:=5},6,9)):Print("matched {V}")
    if(V:=Pick(dup(int){A:=4,B:=5},6,9),V=5)then Print("first {V}")else Print("none")
    for(V:=Pick(pair(int,int){A:=4,B:=5},6,9)):Print("miss {V}")
    for(V:=Pick(pair(int,string){A:=4,B:="x"},"y",9)):Print("mixed {V}")
