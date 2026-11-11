cell:=class{var N:int=0}
token:=class<unique>{V:int}
Child(H:cell,X:t,N:int where t:type)<suspends><allocates>:t=
    defer:Print("cleanup {N}")
    Print("start {N}")
    Obj:=token{V:=N}
    Print("alloc {Obj.V}")
    Sleep(0.1)
    Print("end {N}")
    X
iface(t:type):=interface:
    Launch(H:cell,X:t,N:int)<allocates>:task(t)
carrier(t:type):=class(iface(t)):
    Launch<override>(H:cell,X:t,N:int)<allocates>:task(t)=Start(H,X,N)
Entry(H:cell,X:t,N:int where t:type)<allocates>:task(t)=
    B:iface(t)=carrier(t){}
    B.Launch(H,X,N)
Start(H:cell,X:t,N:int where t:type)<allocates>:task(t)=spawn{Child(H,X,N)}
Main()<suspends>:void=
    H:=cell{N:=19}
    T:=Entry(H,"v10017",40)
    Print("created {H.N}")
    set H.N=119
    T.Cancel()
    Print("cancelled {H.N}")
