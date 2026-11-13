Child()<suspends><reads>:void=
    Print("start 7")
    Sleep(0.01)
    Print("after wait")
Main()<reads>:void=
    T:=spawn{Child()}
    Print("main 7")
