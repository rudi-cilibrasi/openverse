# Edge of the interface-implementation rule (#724): class_z :=
# class(class_x, i_y) {}, with class_x's MethodX() = 1 and i_y's MethodX() =
# 3, a default this time. Epic refuses it when i_y's MethodX is abstract
# (3591, followup-book2/final-method-interface-nonfinal). OpenVerse admits
# it and, as in Java, takes the class chain's method for i_y's slot:
#   through the interface 1
# If Epic takes the interface's default: through the interface 3; it may
# also refuse it as ambiguous.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) admits it (compiled only).
class_x := class:
    MethodX():int = 1

i_y := interface:
    MethodX():int = 3

class_z := class(class_x, i_y) {}

Main():void =
    I:i_y = class_z{}
    Print("OVPROBE through the interface {I.MethodX()}")
