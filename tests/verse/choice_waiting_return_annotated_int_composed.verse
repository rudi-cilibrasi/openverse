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
Use(As:[]int)<suspends>:int =
    Rows:[]int=for(A:As,B:=(Two(2)|Two(4))):return Wait(A+B)
    Print("rows {Rows.Length}")
    -1
Main()<suspends>:void =
    Print("empty {Use(array{})}")
    Print("nonempty {Use(array{3})}")
