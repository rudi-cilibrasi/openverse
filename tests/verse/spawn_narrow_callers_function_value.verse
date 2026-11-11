cell:=class{var N:int=0}
token:=class<unique>{V:int}
Child(H:cell,X:t,N:int where t:type)<suspends><computes>:t=
    defer:Print("cleanup {N}")
    Print("start {N}")
    Sleep(0.1)
    Print("end {N}")
    X
Entry(H:cell,X:t,N:int where t:type)<computes>:task(t)=
    F:type{_(:cell,:t,:int)<computes>:task(t)}=Start
    F(H,X,N)
Start(H:cell,X:t,N:int where t:type)<computes>:task(t)=spawn{Child(H,X,N)}
Main()<suspends>:void=
    H:=cell{N:=18}
    T:=Entry(H,61,11)
    Print("created {H.N}")
    set H.N=118
    V:=T.Await()
    Print("result {V} {H.N}")
