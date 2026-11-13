vehicle:=class<allocates>{var N:int=0}
car:=class<allocates>(vehicle){Name:string="a"}
holder(t:subtype(vehicle)):=class<computes>:
    X:t
    Run()<suspends>:void=
        defer:Print("cleanup {X.N}")
        set X.N=5
        Sleep(10.0)
        Print("bad")
Main()<suspends>:void=
    A:=car{}
    H:=holder(car){X:=A}
    race:
        H.Run()
        block:
            Sleep(0.01)
            Print("winner")
    Print("after {A.N} {A.Name}")
