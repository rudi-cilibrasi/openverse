Arg(N:float,Label:string)<suspends><computes>:float=
    Print(Label)
    Sleep(0.01)
    N
Main()<suspends><reads>:void=
    R:=Lerp(Arg(2.0,"from"),Arg(8.0,"to"),Arg(0.25,"parameter"))
    Y:=Sinh(Arg(0.0,"unary"))
    Sleep(0.01)
    Print("result {R} {Y}")
