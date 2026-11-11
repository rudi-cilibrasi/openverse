# expect: do not allow
cell:=class{var N:int=0}
Child()<suspends><computes>:void=Sleep(0.1)
Start()<computes>:void=
    T:=spawn{Child()}
Bad(H:cell)<computes>:void=
    Start()
    set H.N=7
Main()<suspends>:void=Bad(cell{})
