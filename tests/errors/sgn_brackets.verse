# expect: 5:12: Sgn cannot fail: call it with Sgn(…)
# Sgn of an int or a float always exists.
Main()<decides>:void =
    X := 0
    Y := Sgn[X]
