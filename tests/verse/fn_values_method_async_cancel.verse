cell:=class{var N:int=0}
box(t:type,u:type):=class:
    var V:t
    Extra:u
    C:cell
    Wait(X:[]t)<suspends><transacts>:[]t=
        defer:Print("cleanup {C.N}")
        set C.N+=1
        Print("begin {C.N}")
        Sleep(0.1)
        Print("end {C.N}")
        X+array{V}
Bind(B:box(a,b) where a:type,b:type):type{_(:[]a)<suspends><transacts>:[]a}=B.Wait
Main()<suspends>:void=
    C:=cell{}
    B:=box(int,string){V:=7,Extra:="s",C:=C}
    F:=Bind(B)
    set B.V=8
    R:=F(array{})
    Print("done {R.Length} {R[0] or 0}")
    race:
        F(array{5})
        block:
            Sleep(0.0)
            Print("cancel")
            array{9}
    Print("raced {C.N}")
