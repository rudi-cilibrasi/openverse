# followup-coerce (#724): Does UEFN 43.12 refuse a <decides> function named
# where a function type without <decides> is expected (the Book's
# FunctionTypes.versetest: "no subtyping relationship between functions with
# different async/failing effects", 3509)? Expected refused, a type error;
# OpenVerse refuses it.
# OpenVerse refuses it: expected type{_(:int)<computes>:int}, found
# type{_(:int)<decides><computes>:int}
Check(X:int)<computes><decides>:int = X > 0

Main():void =
    F:type{_(:int)<computes>:int} = Check
    Print("OVPROBE value {F(1)}")
