cell:=class{var N:int=0}
box(t:type):=class:
    V:t
    C:cell
    Later(X:rational)<suspends>:tuple(t,int)=
        set C.N+=1
        Print("begin {C.N} {Floor(X)}")
        defer: Print("cleanup {C.N}")
        Sleep(1.0)
        Print("end {C.N}")
        (V,C.N)
Bind(B:box(t) where t:type)<computes>:type{_(:int)<suspends>:tuple(t,rational)}=B.Later
Main()<suspends>:void=
    B:=box(string){V:="value",C:=cell{}}
    F:=Bind(B)
    T:=spawn{F(3)}
    R:=T.Await()
    Print("done {R(0)} {Floor(R(1))}")
    race:
        F(4)
        block:
            Sleep(0.5)
            Print("cancel")
    Print("finished {B.C.N}")
