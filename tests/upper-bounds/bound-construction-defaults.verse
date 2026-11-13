vehicle:=class<allocates>{var N:int=7}
car:=class<allocates>(vehicle){Name:string="precise"}
counter:=class<allocates>{var N:int=0}
Tick(X:t,C:counter,Digit:int where t:type)<transacts>:t=(set C.N=C.N*10+Digit;X)
ReadN(X:t where t:subtype(vehicle))<reads>:int=X.N
holder(t:subtype(vehicle)):=class<computes>:
    Value:t
    Cached:int=3
    Read(?Y:t=Value)<reads>:int=Y.N
Make(X:t,C:counter,?Y:t=Tick(X,C,1),?N:int=ReadN(Tick(Y,C,2)) where t:subtype(vehicle))<transacts>:holder(t)=holder(t){Value:=Y,Cached:=N}
Later(H:holder(t) where t:subtype(vehicle))<suspends>:int=(Sleep(0.1);H.Read())
Launch(H:holder(t) where t:subtype(vehicle)):task(int)=spawn{Later(H)}
Main()<suspends>:void=
    C:=car{}
    O:=counter{}
    H:=Make(C,O)
    Print("defaults {H.Value.Name} {H.Cached} {H.Read()} {O.N}")
    J:=Make(C,O,?Y:=Tick(C,O,3))
    Print("explicit {J.Value.Name} {J.Cached} {O.N}")
    if(Make(C,O),false?)then Print("bad")else Print("rollback {C.N} {O.N}")
    T:=Launch(H)
    set C.N=9
    Sleep(0.2)
    Print("task {T.Await()} cached {H.Cached} {H.Value.Name}")
