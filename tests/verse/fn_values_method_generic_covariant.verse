animal(t:type):=class{V:t}
dog(t:type):=class(animal(t)){Code:int=1}
base(a:type,b:type):=class:
    V:a
    Extra:b
    Make():animal(a)=animal(a){V:=V}
child(u:type,v:type):=class(base(u,v)):
    Make<override>():dog(u)=dog(u){V:=V}
Bind(P:base(a,b) where a:type,b:type):type{_():animal(a)}=P.Make
BindChild(P:child(a,b) where a:type,b:type):type{_():dog(a)}=P.Make
Main():void=
    B:=child(int,string){V:=7,Extra:="s"}
    F:=Bind(B)
    G:=BindChild(B)
    Print("{F().V} {G().V} {G().Code}")
