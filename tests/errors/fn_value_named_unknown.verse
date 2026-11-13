# expect: expected type{_(?B:int = …):int}, found type{_(?A:int = …):int}
# A function type may not name a parameter the function lacks, optional or not (#503)
F2(?A:int = 2):int = A
Main():void =
    F:type{_(?B:int = 0):int} = F2
    Print("{F()}")
