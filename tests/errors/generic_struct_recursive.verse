# expect: struct b contains itself
wrapper(t:type) := struct:
    Value:t

b := struct:
    Y:?wrapper(b)

Main():void = Print("x")
