# Overloaded functions chosen by the argument's type and by the number of
# arguments, and overloaded methods.
# Tests LANGUAGE.md, Overloading (Book ch. 6): functions of one name told
# apart by their parameters.
# OpenVerse prints (Lean and C agree):
#   int float string | 0 1 2 | int 3 float
Kind(X:int):string = "int"
Kind(X:float):string = "float"
Kind(X:string):string = "string"

Arity():int = 0
Arity(A:int):int = 1
Arity(A:int, B:int):int = 2

meter := class:
    Read(X:int):string = "int {X}"
    Read(X:float):string = "float"

Main():void =
    Print("OVPROBE {Kind(1)} {Kind(1.0)} {Kind("1")}")
    Print("OVPROBE {Arity()} {Arity(5)} {Arity(5, 6)}")
    M := meter{}
    Print("OVPROBE {M.Read(3)} {M.Read(3.0)}")
