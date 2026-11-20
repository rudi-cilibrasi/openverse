# Named parameters with defaults: omitted, given in either order, and a
# default that uses an earlier parameter.
# Tests LANGUAGE.md, Functions: "named parameters ?P:t = default passed as
# ?P := e, after the positional arguments"; "a default may use the
# parameters before it".
# OpenVerse prints (Lean and C agree):
#   box 20 60 2 16 | span 5 2 5
Box(W:int, ?H:int = 1, ?D:int = 10):int = W * H * D

Span(From:int, ?To:int = From + 5):int = To - From

Main():void =
    Print("OVPROBE box {Box(2)} {Box(2, ?H := 3)} {Box(2, ?D := 1)} {Box(2, ?D := 2, ?H := 4)}")
    Print("OVPROBE span {Span(10)} {Span(10, ?To := 12)} {Span(-3)}")
