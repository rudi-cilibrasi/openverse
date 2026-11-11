cell:=class{var N:int=0}
Later(C:cell,X:t,Y:u where t:type,u:type)<suspends>:tuple(t,u)=
    set C.N+=1
    Print("begin {C.N}")
    defer: Print("cleanup {C.N}")
    Sleep(1.0)
    Print("end {C.N}")
    (X,Y)
Bind(X:t,Y:u where t:type,u:type):type{_(:tuple(cell,t,u))<suspends>:tuple(t,u)}=Later
Main()<suspends>:void=
    C:=cell{}
    F:=Bind(3,"s")
    T:=spawn{F((C,7,"x"))}
    R:=T.Await()
    Print("done {R(0)} {R(1)}")
    race:
        F((C,9,"y"))
        block:
            Sleep(0.5)
            Print("cancel")
    Print("finished")
