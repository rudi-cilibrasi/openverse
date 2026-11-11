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
Identity(X:t where t:type)<suspends>:t =
    Sleep(0.1)
    X
Use(As:[]int,X:t,Y:t where t:type)<suspends>:t =
    Rows:[]t=for(A:As):return Identity(X)
    Print("rows {Rows.Length}")
    Y
Main()<suspends>:void =
    Print("empty int {Use(array{},7,9)}")
    Print("empty string {Use(array{},"s","t")}")
    Print("nonempty int {Use(array{2,3},7,9)}")
    Print("nonempty string {Use(array{2,3},"s","t")}")
