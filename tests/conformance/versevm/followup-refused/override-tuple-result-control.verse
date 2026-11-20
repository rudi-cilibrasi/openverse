# Control of override-tuple-result: the override at the overridden signature,
# []int. Not a Book case.
# OpenVerse (ce8632ea, Lean and C agreeing) prints
#   length 2
# If UEFN 43.12 refuses this too, override-tuple-result's refusal is not the
# form's.
getter(t:type) := class<abstract>:
    Get():t

pair_getter := class(getter([]int)):
    Get<override>():[]int = array{1, 2}

Main():void =
    X:getter([]int) = pair_getter{}
    Print("OVPROBE length {X.Get().Length}")
