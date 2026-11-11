cell:=class{var N:int=0}
box(t:type):=class:
    var V:t
    C:cell
    Pair(X:a,Y:b where a:type,b:type):tuple(t,a,b)=
        set C.N+=1
        Print("pair {C.N}")
        (V,X,Y)
Touch(B:box(t) where t:type):box(t)=
    set B.C.N+=1
    Print("receiver {B.C.N}")
    B
Packet(C:cell,X:a,Y:b where a:type,b:type):tuple(a,b)=
    set C.N+=1
    Print("packet {C.N}")
    (X,Y)
Run(B:box(u),X:a,Y:b,Next:u where u:type,a:type,b:type):tuple(u,a,b)=
    F:type{_(:tuple(a,b)):tuple(u,a,b)}=Touch(B).Pair
    set B.V=Next
    P:=Packet(B.C,X,Y)
    F(P)
Main():void=
    R:=Run(box(string){V:="old",C:=cell{}},"old","input","new")
    Print("result {R(0)} {R(1)} {R(2)}")
