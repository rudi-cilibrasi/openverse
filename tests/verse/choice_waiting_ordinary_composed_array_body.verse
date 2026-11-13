Two(N:int)<computes>:int=N|N+1
Early(N:int)<computes>:int=
    if(N<0):return 0
    N|N+1
Run()<suspends>:void=
    R:=for(A:=(Two(1)|Two(3)),A=1,B:=(Two(10)|Two(20)),B=10):
        Sleep(0.01)
        array{A,B}
    for(Row:R):
        if(V0:=Row[0],V1:=Row[1]):Print("array {R.Length} {Row.Length} {V0} {V1}")
Main()<suspends>:void=Run()
