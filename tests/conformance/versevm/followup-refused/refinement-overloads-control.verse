# Control of refinement-overloads: one F, on one refinement. Not a Book case.
# OpenVerse (ce8632ea, Lean and C agreeing) prints
#   small 1
# If UEFN 43.12 refuses this too, refinement-overloads's refusal is not the
# form's.
small := type{_X:int where 0 <= _X, _X < 65535}

F(X:small):int = X

Main():void =
    Print("OVPROBE small {F(1)}")
