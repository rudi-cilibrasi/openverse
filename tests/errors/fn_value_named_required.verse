# expect: expected type{_():int}, found type{_(?A:int):int}
# A function type may leave out only named parameters with defaults (#503)
Need(?A:int):int = A
Main():void =
    F:type{_():int} = Need
    Print("{F()}")
