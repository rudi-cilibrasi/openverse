# expect: 3:0: the value of the constant X depends on itself
# (computing it would never end: a recursion limit at run time before)
X:int = X
Main():void = Print("{X}")
