# expect: <converges> is unsupported on a function with a body
# An override of a <converges> abstract method cannot be <converges>
# itself: it has a body (UEFN 43.12: error 3565; #724).
shape := class<abstract>:
    Area()<converges>:int
square := class(shape):
    Area<override>()<converges>:int = 4
Main():void = Print("{square{}.Area()}")
