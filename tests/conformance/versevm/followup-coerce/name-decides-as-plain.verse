# followup-coerce (#724): Does UEFN 43.12 refuse a <decides> function named
# where a function type without <decides> is expected (the Book's
# FunctionTypes.versetest: "no subtyping relationship between functions with
# different async/failing effects", 3509)? Expected refused, a type error;
# OpenVerse refuses it.
# OpenVerse refuses it: expected type{_(:int)<computes>:int}, found
# type{_(:int)<decides><computes>:int}
# Epic (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, 2026-11-19)
# refuses it: 3509 L11 "This variable expects to be initialized with a value
# of type type{_(:int)<computes>:int}, but this initializer is an
# incompatible value of type type{_(:int)<computes><decides>:int}."
Check(X:int)<computes><decides>:int = X > 0

Main():void =
    F:type{_(:int)<computes>:int} = Check
    Print("OVPROBE value {F(1)}")
