# An abstract class with an abstract method, two concrete subclasses, and a
# method of the abstract class that calls the abstract one.
# Tests LANGUAGE.md, Supported, Classes: "<abstract>", virtual dispatch.
# OpenVerse prints (Lean and C agree):
#   6 7 | 10 20
op_cls := class<abstract>:
    Apply(X:int)<computes>:int
    Twice(X:int)<computes>:int = Apply(Apply(X))

inc_cls := class(op_cls):
    Apply<override>(X:int)<computes>:int = X + 1

dbl_cls := class(op_cls):
    Apply<override>(X:int)<computes>:int = X * 2

Main():void =
    Ops:[]op_cls = array{inc_cls{}, dbl_cls{}}
    for (O : Ops):
        Print("OVPROBE {O.Apply(5)} {O.Twice(5)}")
