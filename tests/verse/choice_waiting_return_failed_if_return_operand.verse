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
    for(A:=(Two(2)|Two(4))):
        return if(N:=array{7}[9])then Wait(N)else Wait(A)
    -1
Main()<suspends>:void=Print("result {Use()}")
