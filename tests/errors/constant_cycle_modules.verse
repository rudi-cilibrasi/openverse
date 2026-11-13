# expect: the value of the constant A.X depends on itself (through Y)
# (a constant may use one defined after it, but not itself through others)
A := module:
    X<public>:int = Y + 1
Y:int = A.X
Main():void = Print("{Y}")
