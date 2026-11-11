Two(N:int)<computes>:int=N|N+1
Early(N:int)<computes>:int=
    if(N<0):return N
    N|N+1
Operand(N:int,Keep:logic)<computes><decides>:[]int=
    Keep?
    array{N}
Run(Keep:logic)<suspends>:[]int=
    var Total:int=0
    defer:
        set Total+=100
        Print("source {Total}")
    Empty:[]int=array{}
    R:=for(A:=Early(-1),set Total+=10,B:=Early(-2),set Total+=20,
        if(B<0)then block:
            defer:
                set Total+=1
                Print("clause {Total}")
            return Operand[Total,Keep]
        else 0,
        C:Empty):
        Sleep(0.0)
        Print("unexpected")
        C
    array{-1}
Main()<suspends>:void=
    for(Keep:array{true,false}):
        R:=Run(Keep)
        Print("result {R[0] or 0}")
