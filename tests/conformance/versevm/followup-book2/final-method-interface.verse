# Book: Tests/Attributes/final.versetest:125 (untagged): class_z inherits
# class_x's MethodX<final>() and an interface's abstract MethodX(). The Book
# refuses it on both VMs, 3591: "A <final> class method and a same-named
# interface method are qualified separately, so the final method does not
# satisfy the interface requirement". OpenVerse keys members by name, takes
# class_x's method for the interface's, and prints
#   defined
# Also asked: final-method-interface-nonfinal (the same without <final>:
# does the rule depend on <final>?). Control:
# final-method-interface-control.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3591 (L16) "Non-abstract class inherits
# abstract function `MethodX` from `i_y` but does not provide an
# implementation.".
class_x := class:
    MethodX<final>():int = 1

i_y := interface:
    MethodX():int

class_z := class(class_x, i_y) {}

Main():void =
    Print("OVPROBE defined")
