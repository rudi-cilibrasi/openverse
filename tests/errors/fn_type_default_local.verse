# expect: unknown identifier 'X' (the default of ?A in a function type
# A type's default may use literals and top-level names only (#503: the Book says nothing of others)
F1(?A:int = 1):int = A
Main():void =
    X:int = 3
    F:type{_(?A:int = X):int} = F1
    Print("{F()}")
