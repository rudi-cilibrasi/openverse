cell:=class{var N:int=0}
box(t:type):=class:
    V:t
    C:cell
    Later(X:[]u where u:type)<suspends>:[]u=
        set C.N+=1
        Print("begin {C.N}")
        defer: Print("cleanup {C.N}")
        Sleep(1.0)
        Print("end {C.N}")
        X
Touch(B:box(t) where t:type):box(t)=
    set B.C.N+=1
    Print("receiver {B.C.N}")
    B
Bind(B:box(t),X:u where t:type,u:type):type{_(:[]u)<suspends>:[]u}=Touch(B).Later
Main()<suspends>:void=
    F:=Bind(box(string){V:="s",C:=cell{}},7)
    T:=spawn{F(array{8,9})}
    R:=T.Await()
    Print("done {R.Length}")
    race:
        F(array{10})
        block:
            Sleep(0.5)
            Print("cancel")
    Print("finished")
