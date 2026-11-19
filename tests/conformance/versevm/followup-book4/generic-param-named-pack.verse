# Edge of the 3509 rule (#724): F(1, 2) of F(X:t, ?E:int = 0 where t:type),
# several arguments for a generic parameter beside a named one. Epic refuses
# them for a tuple and an array parameter
# (followup-book2/overload-tuple-named-call,
# followup-book3/array-named-pack). OpenVerse still packs them into t's
# tuple and prints
#   result 0
# If Epic refuses it (3509), a generic parameter beside a named one takes no
# several arguments either.
F(X:t, ?E:int = 0 where t:type):int = E

Main():void =
    Print("OVPROBE result {F(1, 2)}")
