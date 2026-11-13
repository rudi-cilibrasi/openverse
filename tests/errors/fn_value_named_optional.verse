# expect: expected type{_(?A:int = …):int}, found type{_(?A:int):int}
# A caller of the type may omit A, and the function has no default for it (#503)
F1(?A:int):int = A
Main():void =
    F:type{_(?A:int = 0):int} = F1
    Print("{F(?A := 1)}")
