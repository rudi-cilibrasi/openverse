# expect: shape.Area is <converges>, so Area cannot override it with a body
# A <converges> method without a body is admitted (#724, UEFN 43.12:
# followup-refused/converges-abstract-method), and no method with a body
# overrides it: a body cannot be <converges> (3565), and an override has no
# effect the method it overrides lacks.
shape := class<abstract>:
    Area()<converges>:int
square := class(shape):
    Area<override>()<computes>:int = 4
Main():void = Print("{square{}.Area()}")
