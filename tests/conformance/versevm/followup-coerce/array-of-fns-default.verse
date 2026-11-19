# followup-coerce (#724): Does UEFN 43.12 refuse an array literal of F2 and
# F4 (each with a named, defaulted parameter) where a []type{_():int} is
# expected: its elements joined, as an if's branches are
# (join-named-default-fn), or each named where a function type is expected
# (join-named-default-fn-control)? OpenVerse's rule (if only) leaves it
# admitted. Control: array-of-fns-control.
# OpenVerse (Lean and C agreeing) prints   value 2 | value 4
F2(?A:int = 2):int = A
F4(?B:int = 4):int = B

Main():void =
    Fs:[]type{_():int} = array{F2, F4}
    for (F : Fs):
        Print("OVPROBE value {F()}")
