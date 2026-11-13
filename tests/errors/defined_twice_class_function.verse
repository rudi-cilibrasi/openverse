# expect: 'c' is defined twice (only functions can be overloaded)
# (a class is a definition of its name, as a function is: no overload)
c := class { X:int = 0 }
c(I:int):c = c{X := I}
Main():void = {}
