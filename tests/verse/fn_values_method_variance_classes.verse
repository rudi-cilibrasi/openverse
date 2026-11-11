animal(t:type):=class{V:t}
dog(t:type):=class(animal(t)){N:int=7}
box(t:type,h:type):=class:
    Hidden:h
    Make(A:animal(t))<computes>:dog(t)=dog(t){V:=A.V}
Bind(B:box(t,h) where t:type,h:type)<computes>:type{_(:dog(t))<computes>:animal(t)}=B.Make
Main():void=
    F:=Bind(box(string,int){Hidden:=3})
    R:=F(dog(string){V:="dog"})
    Print(R.V)
