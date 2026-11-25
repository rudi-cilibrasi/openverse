# expect: expected type{_(:int):int}, found type{_(:any):int}
# A function named at a function type with an any result is converted
# (#724, tests/verse/fn_named_any_result); one with an any parameter named
# where another parameter type is expected is not: Epic's answer is not
# recorded (followup-variance/any-param asks it of a function value).
AnyP(X:any):int = 7
CallI(G(:int):int):int = G(4)
Main():void =
    Print("{CallI(AnyP)}")
