Two(N:int)<computes>:int=N|N+1
Early(N:int)<computes>:int=
    if(N<0):return N
    N|N+1
Run(Next:int)<suspends>:[][]int=
    var Total:int=0
    R:=for(A:=Early(-1),(set Total+=A; true?),B:=Early(-2),(set Total+=B; true?),C:=Early(Next)):
        Sleep(0.01)
        set Total+=C
        Print("body {A} {B} {C} {Total}")
        array{A,B,C}
    Print("end {Total}")
    R
Main()<suspends>:void=
    for(K:array{-3,3}):
        R:=Run(K)
        Print("rows {R.Length}")
        for(Row:R):Print("rank {Row.Length} {Row[2] or 0}")
