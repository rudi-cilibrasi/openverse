# Control of fbounded-class: the parent's type argument another class. Not a
# Book case.
# OpenVerse (ce8632ea, Lean and C agreeing) prints
#   clone 13
# If UEFN 43.12 refuses this too, fbounded-class's refusal is not the form's.
cloneable(t:type) := interface:
    Clone()<transacts>:t

other := class:
    Value:int

item := class(cloneable(other)):
    Value:int
    Clone<override>()<transacts>:other = other{Value := Value}

Main():void =
    X:cloneable(other) = item{Value := 13}
    Y := X.Clone()
    Print("OVPROBE clone {Y.Value}")
