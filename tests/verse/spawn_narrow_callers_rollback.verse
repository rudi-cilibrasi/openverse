Child()<suspends><computes>:void=
    defer:Print("child cleanup")
    Print("child start")
    Sleep(0.1)
    Print("child end")
Outer()<computes>:int=Inner()
Inner()<computes>:int=Start()
Start()<computes>:int=
    T:=spawn{Child()}
    7
Main()<suspends>:void=
    if(V:=Outer(),false?)then Print("unexpected")else Print("failed")
    Sleep(0.2)
    Print("done")
