# expect: in c, b.M does not have the signature of i.M
# (#724: a class implements an interface's abstract method itself, or a class
# below the interface does: a method of its name from a class that is not below
# the interface is that class's own; UEFN 43.12 error 3591,
# followup-book2/final-method-interface)
i := interface:
    M():string = "i"
b := class:
    M():int = 42
c := class(b, i):
    X:int = 0
Main():void = Print("x")
