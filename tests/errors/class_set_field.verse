# expect: field 'N' of class counter is not a var
# Only var fields of a class can be set (#34): the object is shared.
counter := class:
    N:int = 0
Main():void =
    var C:counter = counter{}
    set C.N = 10
