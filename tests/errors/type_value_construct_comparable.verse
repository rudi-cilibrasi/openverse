# expect: C1{…} constructs through a value of concrete_subtype(comparable), which need not be a class's: it cannot be constructed
c := class<unique><concrete>:
    S:string = ""
Main():void =
    C1:concrete_subtype(comparable) = c
    D := C1{}
