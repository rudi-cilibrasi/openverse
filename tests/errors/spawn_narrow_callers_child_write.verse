# expect: do not allow
cell:=class{var N:int=0}
Child(H:cell)<suspends><writes>:void=
    set H.N=7
    Sleep(0.1)
Start(H:cell)<computes>:void=
    T:=spawn{Child(H)}
Main()<suspends>:void=Start(cell{})
