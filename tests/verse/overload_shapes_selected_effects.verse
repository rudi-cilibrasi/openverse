cell := class:
    var N:int = 0
F(X:int,Y:int)<decides>:int = X+Y
F(X:string):int = 0
G(X:int,Y:int)<computes>:int = X+Y
G(X:string)<suspends>:int = X.Length
H(X:int,Y:int)<computes>:int = X+Y
H(X:cell)<reads><writes>:int =
    set X.N += 1
    X.N
Pure()<computes>:int = H((3,4))
Main():void =
    if(R:=F[(1,2)])then Print("decides {R}")else Print("wrong")
    Print("immediate {G((2,3))}")
    Print("pure {Pure()}")
