Two(N:int)<computes>:int=N|N+1
Early(N:int)<computes>:int=
    if(N<0):return 0
    N|N+1
Run()<suspends>:[]int=
    var Total:int=0
    defer:Print("source {Total}")
    for(A:=(Two(1)|Two(3)),set Total+=A,B:=Early(10)):
        defer:
            set Total+=100
            Print("body cleanup {Total}")
        Sleep(0.01)
        return array{A,B,Total}
    array{}
Main()<suspends>:void=
    R:=Run()
    if(A:=R[0],B:=R[1],C:=R[2]):Print("return {R.Length} {A} {B} {C}")
