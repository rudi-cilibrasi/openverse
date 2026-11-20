# Control of type-argument-array: the type argument a name, int. Not a Book
# case.
# OpenVerse (ce8632ea, Lean and C agreeing) prints
#   outer 2
# If UEFN 43.12 refuses this too, type-argument-array's refusal is not the
# form's.
Pair(t:type, X:t):[]t = array{X, X}

Main():void =
    A := Pair(int, 1)
    Print("OVPROBE outer {A.Length}")
