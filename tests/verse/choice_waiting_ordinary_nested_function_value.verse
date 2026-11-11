Two(N:int)<computes>:int=N|N+1
Early(N:int)<computes>:int=
    if(N<0):return 0
    N|N+1
Wait(N:int)<suspends><computes>:int=
    Sleep(0.2)
    N
Run(F:type{_(:int)<suspends>:int})<suspends>:void=
    var Total:int=7
    branch:
        Sleep(0.1)
        set Total=31
    R:=for(A:=(Two(1)|Two(3)),A=1,B:=Early(10),B=10):
        Inner:=for(C:=(Two(20)|Two(22)),C=20,D:=Early(30),D=30):
            V:=F(A+B+C+D)
            V+Total
        Inner
    for(Row:R):
        if(V:=Row[0]):Print("nested {R.Length} {Row.Length} {V} {Total}")
Main()<suspends>:void=Run(Wait)
