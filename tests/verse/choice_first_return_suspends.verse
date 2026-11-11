Two(N:int):int=N|N+1
Run()<suspends>:int=
    var Total:int=0
    defer:
        set Total+=100
        Print("source {Total}")
    branch:
        defer:
            set Total+=1
            Print("earlier {Total}")
        Sleep(1.0)
    branch:
        defer:
            set Total+=10
            Print("later {Total}")
        Sleep(1.0)
    Sleep(0.0)
    if(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2)),set Total+=A+B,if(A=0)then return Total else 0):
        Print("normal {Total}")
    Total
Main()<suspends>:void=Print("result {Run()}")
