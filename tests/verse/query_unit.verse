counter := class:
    var Count:int = 0

Touch(C:counter)<transacts>:void =
    set C.Count += 1
    Print("touch")

Fail(C:counter)<transacts><decides>:void =
    set C.Count += 10
    Print("hidden")
    false?

Main():void =
    C := counter{}
    if (Touch(C)?) then Print("wrong") else Print("void false")
    Print("count {C.Count}")
    if ((not Fail[C])?) then Print("wrong") else Print("not false")
    Print("count {C.Count}")
    U:true = false
    if (U?) then Print("wrong") else Print("unit false")
    if (()?) then Print("wrong") else Print("literal false")
    O:?void = option{Touch(C)}
    if (O??) then Print("wrong") else Print("option value false")
    Print("count {C.Count}")
