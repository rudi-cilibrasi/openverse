vehicle:=class<allocates>{var N:int=7}
car:=class<allocates>(vehicle){Name:string="precise"}
Keep(A:t where t:subtype([]vehicle))<computes>:t=A
Wait(A:t where t:subtype([]vehicle))<suspends>:int=
    defer:
        if(V:=A[0])then Print("cleanup {V.N}")else Print("empty cleanup")
    Sleep(0.1)
    if:
        V:=A[0]
    then:
        set V.N+=1
        V.N
    else:
        -1
Launch(A:t where t:subtype([]vehicle)):task(int)=spawn{Wait(A)}
Main()<suspends>:void=
    C:=car{}
    A:=Keep(array{C})
    T:=Launch(A)
    set C.N=10
    Sleep(0.2)
    R:=T.Await()
    Print("task {R} {C.Name}")
    race:
        Wait(A)
        block:
            Sleep(0.05)
            Print("winner")
            0
    Print("cancel {C.N} {C.Name}")
