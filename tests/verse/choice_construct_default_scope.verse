# Defaults have their declaration locals and their inherited home's type arguments.
slot := struct { A:int = block{N := 7; N}; B:int }
base(t:type) := class:
    E:[]t = block{V:[]t = Concatenate(); V}
    B:int
child(u:type) := class(base(tuple(char, u))) {}
Read(P:child(string)):int =
    E:[]tuple(char, string) = P.E
    P.B + E.Length
Main():void =
    N := 99
    for (P := slot{B := 1 | 2}):
        Print("scope {P.A} {P.B} {N}")
    for (V := Read(child{B := 1 | 2})):
        Print("inherited {V}")
