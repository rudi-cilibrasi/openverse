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
Entry(H:cell,X:t,N:int where t:type)<reads>:task(t)=B(H,X,N,3)
B(H:cell,X:t,N:int,D:int where t:type)<reads>:task(t)=A(H,X,N,D)
A(H:cell,X:t,N:int,D:int where t:type)<reads>:task(t)=
    if(D<=0):return Start(H,X,N)
    B(H,X,N,D-1)
Start(H:cell,X:t,N:int where t:type)<reads>:task(t)=spawn{Child(H,X,N)}
Main()<suspends>:void=
    H:=cell{N:=18}
    T:=Entry(H,"v10011",10)
    Print("created {H.N}")
    set H.N=118
    T.Cancel()
    Print("cancelled {H.N}")
