Two(N:int)<computes>:int=N|N+1
Early(N:int)<computes>:int=
    if(N<0):return 0
    N|N+1
Run()<suspends><computes>:void=
    var Total:int=7
    branch:
        Sleep(0.1)
        set Total=99
    for(A:=Early(1),B:=(Two(10)|Two(20)),C:=Early(30)):
        Sleep(0.2)
        Print("readonly {A} {B} {C} {Total}")
    Print("end {Total}")
Main()<suspends>:void=Run()
