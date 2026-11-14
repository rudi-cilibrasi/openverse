Two(N:int)<computes>:int=N|N+1
Early(N:int)<computes>:int=
    if(N<0):return 0
    N|N+1
Run()<suspends>:void=
    var Total:int=0
    R:=for(A:=(Two(1)|Two(3)),(set Total+=A; true?),A=1,B:=Early(10)):
        Sleep(0.01)
        set Total+=B
        Print("body {A} {B} {Total}")
    Print("end {R.Length} {Total}")
Main()<suspends>:void=Run()
