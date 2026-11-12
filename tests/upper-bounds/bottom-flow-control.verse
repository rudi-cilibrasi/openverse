vehicle:=class<computes>{N:int=7}
car:=class<computes>(vehicle){Name:string="precise"}
Return(X:car)<computes>:car=return X
Main():void=
    loop:
        break
        Print("bad")
    R:=Return(car{})
    Print("bottom {R.Name} {R.N}")
