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
VoidWait(N:int)<suspends>:void =
    Print("begin {N}")
    Sleep(0.1)
    Print("end {N}")
Use()<suspends>:void =
    defer:Print("source")
    for(A:=2|3):
        defer:Print("body")
        return VoidWait(A)
Main()<suspends>:void =
    Use()
    Print("done")
