# The result is an int past 64 bits (#724), whose ToString is the overflow error
Main():void=
    V:rational=-9223372036854775807-1
    Print("before")
    Print("{Floor(-V)}")
