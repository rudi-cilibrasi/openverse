# expect: it can fail (the default of ?A in a function type
# A type's default cannot fail, as a function's cannot (#503)
Fails()<decides>:int = 0 = 1
F1(?A:int = 1):int = A
Main():void =
    F:type{_(?A:int = Fails[]):int} = F1
    Print("{F()}")
