Child()<suspends><computes>:void=
    Print("start")
    Sleep(0.01)
    Print("after wait")
Main()<computes>:void=
    T:=spawn{Child()}
