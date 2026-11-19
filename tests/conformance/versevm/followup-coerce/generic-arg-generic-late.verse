# followup-coerce (#724): generic-arg-generic with the function last, after
# the argument that gives the type parameter. OpenVerse admits it.
# OpenVerse (Lean and C agreeing) prints   value 1
Identity(X:t where t:type):t = X
Apply(X:t, F(:t):t where t:type):t = F(X)

Main():void =
    Print("OVPROBE value {Apply(1, Identity)}")
