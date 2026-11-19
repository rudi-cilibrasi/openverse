# Names that differ only in case that Epic's toolchain tells apart (#724):
# other parameter types (UEFN 43.12 admits Function(Value:int) beside
# FUNCTION(), followup-book2/case-collision-module-fn-control, and runs
# it: lower 42, upper 420; the Book's FORT-793952 :19-63, :106-150: int and
# float, two classes, a class and its option, <suspends> beside a function
# that is not), and names in different classes or modules, or of a function
# and a constant.
Function(Value:int):int = Value
FUNCTION():int = 420
Twice(X:int):int = X * 2
TWICE(X:float):int = 3
Wait()<suspends>:int = 7
WAIT():int = 8
first_class := class:
    Get():int = 1
second_class := class:
    GET():int = 2
mm := module:
    Count<public>():int = 5
COUNT:int = 6
Main()<suspends>:void =
    Print("lower {Function(42)} upper {FUNCTION()}")
    Print("twice {Twice(4)} {TWICE(4.0)}")
    W := Wait()
    Print("wait {W} {WAIT()}")
    Print("classes {first_class{}.Get()} {second_class{}.GET()}")
    Print("count {mm.Count()} {COUNT}")
