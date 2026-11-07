# expect: b.Make must have the signature of a.Make
pet := class:
    N:int = 0
a := class:
    Make():pet = pet{}
b := class(a):
    Make<override>():int = 1
Main():void = Print("x")
