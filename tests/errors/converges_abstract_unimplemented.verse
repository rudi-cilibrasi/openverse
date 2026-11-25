# expect: square must implement Area
# A class that is not <abstract> below a <converges> abstract method has
# no implementation of it, and can have none (#724, converges_override).
shape := class<abstract>:
    Area()<converges>:int
square := class(shape):
    Side:int = 2
Main():void = Print("{square{}.Side}")
