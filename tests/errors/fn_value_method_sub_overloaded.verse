# expect: 'M' is an overloaded method of child
base := class:
    M(X:int):int = X + 1
child := class(base):
    M(X:string):string = X
Main():void =
    F := child{}.M
    Print("x")
