animal(t:type):=class{V:t}
dog(t:type):=class(animal(t)){N:int=7}
base(t:type):=class:
    Make(X:animal(t))<computes>:animal(t)=X
child(a:type,h:type):=class(base(a)):
    Hidden:h
    Make<override>(X:animal(a))<computes>:dog(a)=dog(a){V:=X.V}
Bind(B:child(t,u) where t:type,u:type)<computes>:type{_(:dog(t))<computes>:animal(t)}=B.Make
BindBase(B:base(t) where t:type)<computes>:type{_(:dog(t))<computes>:animal(t)}=B.Make
Main():void=
    B:=child(string,int){Hidden:=3}
    F:=Bind(B)
    G:=BindBase(B)
    Print(F(dog(string){V:="child"}).V)
    Print(G(dog(string){V:="base"}).V)
