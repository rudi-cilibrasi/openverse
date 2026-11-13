# expect: expected int, found char (the default of ?A in a function type
# A type's default is checked at the parameter's type (Book DefaultNamed tests, #503)
F1(?A:int = 1):int = A
Main():void =
    F:type{_(?A:int = 'a'):int} = F1
    Print("{F()}")
