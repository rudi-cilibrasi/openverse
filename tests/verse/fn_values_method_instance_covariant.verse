animal(t:type):=class:
    V:t
dog(t:type):=class(animal(t)):
    Bark():string="woof"
base:=class:
    Make(X:u where u:type):animal(u)=animal(u){V:=X}
child:=class(base):
    Make<override>(X:v where v:type):dog(v)=dog(v){V:=X}
Main():void=
    C:=child{}
    F:type{_(:int):dog(int)}=C.Make
    G:type{_(:int):animal(int)}=C.Make
    H:type{_(:string):animal(string)}=base{}.Make
    Print("{F(3).Bark()} {F(4).V} {G(5).V} {H("s").V}")
