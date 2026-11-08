# expect: expected type{_(:int):string}, found type{_(:int):int}
# parameter and result types must match exactly
D(X:int):int = X
Main():void =
    F:int->string = D
    Print(F(1))
