# expect: field 'M' of b has the name of an inherited method
a := class:
    M():int = 1
b := class(a):
    M:int = 2
Main():void = Print("x")
