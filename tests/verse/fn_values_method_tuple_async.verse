cell:=class{var N:int=0}
box(t:type):=class:
    V:t
    C:cell
    Later(X:a,Y:b where a:type,b:type)<suspends>:tuple(a,b)=
        set C.N+=1
        Print("begin {C.N}")
        defer: Print("cleanup {C.N}")
        Sleep(1.0)
        Print("end {C.N}")
        (X,Y)
Touch(B:box(t) where t:type):box(t)=
    set B.C.N+=1
    Print("receiver {B.C.N}")
    B
Run(B:box(t),X:a,Y:b where t:type,a:type,b:type)<suspends>:void=
    F:type{_(:tuple(a,b))<suspends>:tuple(a,b)}=Touch(B).Later
    T:=spawn{F((X,Y))}
    R:=T.Await()
    Print("done {B.C.N}")
    race:
        F((X,Y))
        block:
            Sleep(0.5)
            Print("cancel")
    Print("finished")
Main()<suspends>:void=Run(box(int){V:=7,C:=cell{}},3,27)
