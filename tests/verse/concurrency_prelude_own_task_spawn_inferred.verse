task(t:type):=class{N:int=7}
Child()<suspends>:int=8
Main()<suspends>:void=
    T:=spawn{Child()}
    Print("{T.Await()} {task(int){}.N}")
