# expect: expected t, found int
# A default is checked once, for every type argument, even if never used.
box(t:type) := struct:
    Value:t = 0

Main():void = Print("x")
