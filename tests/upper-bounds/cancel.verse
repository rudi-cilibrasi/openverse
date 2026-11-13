vehicle:=class<allocates>{var N:int=0}
car:=class<allocates>(vehicle){Name:string="a"}
Worker(X:t where t:subtype(vehicle))<suspends>:void=
    defer:Print("cleanup {X.N}")
    set X.N=5
    Sleep(10.0)
    Print("bad")
Main()<suspends>:void=
    A:=car{}
    race:
        Worker(A)
        block:
            Sleep(0.0)
            Print("winner")
    Print("after {A.N} {A.Name}")
