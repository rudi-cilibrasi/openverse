vehicle:=class<allocates>{var N:int=1}
car:=class<allocates>(vehicle){Name:string="precise"}
worker(a:subtype(vehicle)):=class<computes>:
    Item:a
    Work(X:vehicle)<suspends>:a=
        defer:Print("cleanup {Item.N}")
        set X.N+=1
        Sleep(0.1)
        Item
Build(X:t where t:subtype(vehicle))<computes>:type{_(:t)<suspends>:vehicle}=worker(t){Item:=X}.Work
Main()<suspends>:void=
    C:=car{}
    F:=Build(C)
    set C.N=7
    R:=F(C)
    Print("result {C.Name} {R.N}")
    race:
        F(C)
        block:
            Sleep(0.05)
            Print("winner")
            C
    Print("done {C.Name} {C.N}")
