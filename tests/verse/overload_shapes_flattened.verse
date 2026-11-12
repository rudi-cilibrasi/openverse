# Flattened domains distinguish declarations, then guide tuple expansion.
F(X:tuple(int,int)):string = "tuple {X(0)+X(1)}"
F(X:string,Y:string):string = "strings {X}{Y}"
G(X:tuple(string,string)):string = "tuple {X(0)}{X(1)}"
G(X:int,Y:int):string = "ints {X+Y}"
Main():void =
    Print(F((1,2)))
    Print(F("a","b"))
    Print(F(("c","d")))
    Print(G(("e","f")))
    Print(G(3,4))
    Print(G((5,6)))
