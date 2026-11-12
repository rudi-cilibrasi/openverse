ca:=class:
    M(?X:void=branch{Sleep(0.1);Print("late a")})<suspends>:int=1
cb:=class:
    M(?X:void=branch{Sleep(0.1);Print("late b")})<suspends>:int=2
Dup(X:t where t:type)<computes>:t=X|X
Main()<suspends>:void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{}))):
        V:=A.M()
        Sleep(0.2)
        Print("body {V}")
        V
    Print("done {Rows.Length}")
