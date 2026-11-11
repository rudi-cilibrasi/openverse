Later(X:t where t:type)<suspends>:t=
    Print("begin")
    defer: Print("cleanup")
    Sleep(1.0)
    Print("end")
    X
Bind(X:t where t:type):type{_(:t)<suspends>:t}=Later
Main()<suspends>:void=
    F:=Bind(array{3})
    T:=spawn{F(array{7,8})}
    R:=T.Await()
    Print("done {R.Length}")
    race:
        F(array{9})
        block:
            Sleep(0.5)
            Print("cancel")
    Print("finished")
