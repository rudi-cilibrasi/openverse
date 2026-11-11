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
Use()<suspends>:int =
    defer:Print("source")
    loop:
        defer:Print("loop")
        for(A:=1|2,if(A=1)then break else Print("bad filter")):
            return Wait(A)
        Print("bad suffix")
    Print("after")
    7
Main()<suspends>:void=Print("result {Use()}")
