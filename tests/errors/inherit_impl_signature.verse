# expect: in c, b.M does not have the signature of i.M
i := interface:
    M():string
b := class:
    M():int = 42
c := class(b, i):
    X:int = 0
Main():void = Print("x")
