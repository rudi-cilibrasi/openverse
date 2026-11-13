vehicle:=class<allocates>{var N:int=7}
car:=class<allocates>(vehicle){Name:string="precise"}
counter:=class<allocates>{var N:int=0}
Tick(X:t,C:counter,Digit:int where t:type)<transacts>:t=(set C.N=C.N*10+Digit;X)
Read(X:car)<reads>:int=X.N
holder:=class<computes>:
    Value:car
    Cached:int=3
    Read(?Y:car=Value)<reads>:int=Y.N
Make(X:car,C:counter,?Y:car=Tick(X,C,1),?N:int=Read(Tick(Y,C,2)))<transacts>:holder=holder{Value:=Y,Cached:=N}
Later(H:holder)<suspends>:int=(Sleep(0.1);H.Read())
Launch(H:holder):task(int)=spawn{Later(H)}
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
