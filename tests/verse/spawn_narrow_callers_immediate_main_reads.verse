cell:=class{var N:int=7}
Child(H:cell)<suspends><reads>:void=
    Print("start {H.N}")
    Sleep(0.0)
    Print("after wait")
Main()<reads>:void=
    H:=cell{}
    T:=spawn{Child(H)}
    Print("main {H.N}")
