vehicle:=class<allocates>{var N:int=7}
car:=class<allocates>(vehicle){Name:string="precise"}
counter:=class<allocates>{var N:int=0}
Take(A:t,C:counter where t:subtype([]vehicle))<transacts>:t=
    set C.N=C.N*10+1
    A
Index(C:counter)<transacts>:int=
    set C.N=C.N*10+2
    0
Bump(A:t,C:counter where t:subtype([]vehicle))<transacts>:int=
    if:
        V:=Take(A,C)[Index(C)]
    then:
        set V.N+=1
        V.N
    else:
        -1
Main():void=
    C:=car{}
    A:=array{C}
    Order:=counter{}
    Print("first {Bump(A,Order)} order {Order.N}")
    if(Bump(A,Order),false?)then Print("bad")else Print("rollback {C.N} {Order.N}")
    set C.N=20
    Print("alias {Bump(A,Order)} {C.Name} {Order.N}")
