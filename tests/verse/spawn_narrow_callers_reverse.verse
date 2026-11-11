cell:=class{var N:int=0}
token:=class<unique>{V:int}
Child(H:cell,X:t,N:int where t:type)<suspends><computes>:t=
    defer:Print("cleanup {N}")
    Print("start {N}")
    Sleep(0.1)
    Print("end {N}")
    X
Entry(H:cell,X:t,N:int where t:type)<computes>:task(t)=Middle(H,X,N)
Middle(H:cell,X:t,N:int where t:type)<computes>:task(t)=Start(H,X,N)
Start(H:cell,X:t,N:int where t:type)<computes>:task(t)=spawn{Child(H,X,N)}
Main()<suspends>:void=
    H:=cell{N:=15}
    T:=Entry(H,"v10005",35)
    Print("created {H.N}")
    set H.N=115
    T.Cancel()
    Print("cancelled {H.N}")
