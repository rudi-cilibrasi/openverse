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
box(t:type) := class:
    V:t
    Get()<suspends>:t =
        Sleep(0.1)
        V
intbox := class(box(int)):
    Get<override>()<suspends>:int =
        Sleep(0.1)
        V+1
Use(B:box(t) where t:type)<suspends>:t =
    for(A:=(Two(0)|Two(2))):return B.Get()
    B.V
Main()<suspends>:void =
    Print("int {Use(intbox{V:=7})}")
    Print("string {Use(box(string){V:="s"})}")
