token:=class<allocates><unique>{V:int}
Child()<suspends><allocates>:void=
    Obj:=token{V:=7}
    Print("start {Obj.V}")
    Sleep(0.0)
    Print("after wait")
Main()<allocates>:void=
    T:=spawn{Child()}
