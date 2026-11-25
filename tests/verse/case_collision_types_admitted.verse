# Types whose names differ only in case in different modules, and a
# function and a constant so named (#724): only one scope's types collide
# (UEFN 43.12 admits a function and a constant, followup-book3/
# case-collision-function-constant, and a method beside a subclass's,
# case-collision-inherited).
mm := module:
    cc<public> := class:
        V<public>:int = 1
CC := class:
    V:int = 2
Function():int = 42
FUNCTION:int = 420
base_class := class:
    Get():int = 3
derived_class := class(base_class):
    GET():int = 4
Main():void =
    Print("types {mm.cc{}.V} {CC{}.V}")
    Print("names {Function()} {FUNCTION}")
    D := derived_class{}
    Print("methods {D.Get()} {D.GET()}")
