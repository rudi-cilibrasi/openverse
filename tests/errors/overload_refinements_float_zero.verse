# expect: parameters a call cannot tell apart, (pos) and (neg)
# 0.0 and -0.0 are one number: refinements that both hold it overlap
# (#724, tests/verse/overload_refinements).
pos := type{_X:float where _X >= 0.0}
neg := type{_X:float where _X <= -0.0}
H(X:pos):float = X
H(X:neg):float = X + 1.0
Main():void =
    Print("{H(1.0)}")
