Two(N:int):int=N|N+1
Down(N:int)<computes><decides>:int =
    N>=0
    N|Down[N-1]
Wait(N:int)<suspends>:int =
    Print("begin {N}")
    Sleep(0.1)
    Print("end {N}")
    N+10
pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
cell := class { var N:int=5 }
Operand(N:int)<suspends>:int =
    defer:Print("wait cleanup {N}")
    Print("begin {N}")
    Sleep(0.1)
    Print("end {N}")
    N+10
Use(C:cell)<suspends>:int =
    defer:Print("source {C.N}")
    branch:
        defer:Print("observer stop {C.N}")
        Sleep(0.05)
        set C.N=20
        Print("observer {C.N}")
        Sleep(1.0)
    for(A:=1|2,B:=3|4):
        defer:
            set C.N+=100
            Print("body {C.N}")
        set C.N=7
        return Operand(C.N)
    -1
Main()<suspends>:void=Print("result {Use(cell{})}")
