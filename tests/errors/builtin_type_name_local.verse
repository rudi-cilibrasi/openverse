# expect: 5:4: 'string' is the name of a built-in type
# Nor does a local, whose uses would read the type: X would be the type
# string, not the local.
Main():void =
    string:int = 1
    X:type = string
    Print("x")
