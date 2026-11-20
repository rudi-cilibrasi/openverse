# Several arguments passed to a function whose one parameter is a tuple:
# packed into the tuple.
# Tests LANGUAGE.md, Functions: "positional arguments pack into a single
# tuple parameter, including tuple() and singleton tuples".
# OpenVerse prints (Lean and C agree):
#   12 56 34
Sum2(P:tuple(int, int)):int = P(0) * 10 + P(1)

Main():void =
    T := (3, 4)
    Print("OVPROBE {Sum2(1, 2)} {Sum2((5, 6))} {Sum2(T)}")
