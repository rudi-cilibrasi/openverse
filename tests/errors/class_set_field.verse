# expect: field 'N' of class counter cannot be set
# Setting a class field would make the tuple representation observable
# (D := C; set C.N = 10 would leave D.N at 0).
counter := class:
    N:int = 0
Main():void =
    var C:counter = counter{}
    set C.N = 10
