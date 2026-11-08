# expect: a value of type type{_(:int)<decides>:int} can fail: call it with […]
D(X:int):int = X
Main():void =
    F:type{_(:int)<decides>:int} = D
    Print("{F(1)}")
