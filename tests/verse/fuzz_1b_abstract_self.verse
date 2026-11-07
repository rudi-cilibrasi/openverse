# internal error: a.N does not pass Prog.checkTypes: Self of an abstract class
# with no concrete class below it, used as its parent class.
b := class:
    V:int = 1
a := class<abstract>(b):
    N():b = Self
Main():void =
    Print("x")
