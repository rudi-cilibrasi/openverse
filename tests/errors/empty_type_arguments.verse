# expect: 6:4: pair is parametric: write pair(…) with 1 type argument(s)
# `t()` is `t` with no type arguments, which a parametric type does not take.
pair(t:type) := struct:
    First:t
Main():void =
    X:pair() = pair(){First := 1}
