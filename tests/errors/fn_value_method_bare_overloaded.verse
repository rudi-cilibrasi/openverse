# expect: 'M' is an overloaded method of c: an overloaded method cannot be used as a value
c := class:
    M(X:int):int = X
    M(X:string):string = X
    Get():int->int = M
Main():void = Print("x")
