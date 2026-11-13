vehicle:=class<allocates>{var N:int=1}
car:=class<allocates>(vehicle){Name:string="precise"}
worker:=class<computes>:
    Item:car
    Work(X:vehicle)<suspends>:car=
        defer:Print("cleanup {Item.N}")
        set X.N+=1
        Sleep(0.1)
        Item
Build(X:car)<computes>:type{_(:car)<suspends>:vehicle}=worker{Item:=X}.Work
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
