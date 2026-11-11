Wait(N:int)<suspends>:int =
    Sleep(0.01)
    N
Use()<suspends>:int =
    for(A:=1|2,B:=1|2):
        return Wait(A+B)
    -1
Main()<suspends>:void = Print("{Use()}")
