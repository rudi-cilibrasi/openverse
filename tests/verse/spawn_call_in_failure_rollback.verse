# A task spawned by a call in a failure context that then fails is undone
# with it: its first run, up to its first wait, is rolled back, and it never
# runs again (the callers are <transacts>, as a spawn's effects are, the
# Book's tests, Effects.versetest)
Child()<suspends><computes>:void=
    defer:Print("child cleanup")
    Print("child start")
    Sleep(0.1)
    Print("child end")
Outer()<transacts>:int=Inner()
Inner()<transacts>:int=Start()
Start()<transacts>:int=
    T:=spawn{Child()}
    7
Main()<suspends>:void=
    if(V:=Outer(),false?)then Print("unexpected")else Print("failed")
    Sleep(0.2)
    Print("done")
