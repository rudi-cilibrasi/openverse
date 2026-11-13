vehicle:=class<computes>{N:int=7}
car:=class<computes>(vehicle){Name:string="precise"}
Keep(X:t where t:subtype(vehicle))<computes>:t=X
Return(X:t where t:subtype(vehicle))<computes>:t=Keep(return X)
Main():void=
    loop:
        V:vehicle=Keep(break)
        Print("bad")
    R:=Return(car{})
    Print("bottom {R.Name} {R.N}")
