# expect: 4:0: 'C' is defined twice (only functions can be overloaded)
# (the first was kept silently: C{}.X ran)
C := class { X:int = 1 }
C := class { Y:int = 2 }
Main():void = Print("{C{}.X}")
