cell:=class{var N:int=0}
token:=class<unique>{V:int}
Child(H:cell,X:t,N:int where t:type)<suspends><reads>:t=
    defer:Print("cleanup {N}")
    Print("start {N}")
    Print("read {H.N}")
    Sleep(0.1)
    Print("late {H.N}")
    Print("end {N}")
    X
Entry(H:cell,X:t,N:int where t:type)<reads>:task(t)=Named(H,X)
Named(H:cell,X:t,?N:int=12 where t:type)<reads>:task(t)=Start(H,X,N)
Start(H:cell,X:t,N:int where t:type)<reads>:task(t)=spawn{Child(H,X,N)}
Main()<suspends>:void=
    H:=cell{N:=14}
    T:=Entry(H,62,12)
    Print("created {H.N}")
    set H.N=114
    V:=T.Await()
    Print("result {V} {H.N}")
