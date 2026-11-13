# expect: a value of type type{_(?A:int):int} needs the argument ?A
# A call through a value gives every name its type requires (#503)
Need(?A:int):int = A
Main():void =
    F:type{_(?A:int):int} = Need
    Print("{F()}")
