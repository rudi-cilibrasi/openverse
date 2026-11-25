# Control of override-parametric-result: the override at the overridden
# signature, comparable. Not a Book case.
# OpenVerse (ce8632ea, Lean) refuses it: "boxing a value of type $ext0 as a
# comparable here is not supported yet"; if it ran it would print method gives
# 3.
# If UEFN 43.12 refuses this too, override-parametric-result's refusal is not
# the form's.
# That refusal is a gap of OpenVerse's own (a field of type
# t:subtype(comparable) returned as a comparable), and its message names an
# internal type, $ext0.
super_class := class<abstract>:
    Method():comparable

sub_class(t:subtype(comparable)) := class(super_class):
    Field:t
    Method<override>():comparable = Field

Main():void =
    X:super_class = sub_class(int){Field := 3}
    V := X.Method()
    if (V = 3):
        Print("OVPROBE method gives 3")
