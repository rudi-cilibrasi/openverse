# final-method-interface without <final>: class_z inherits class_x's
# MethodX() and an interface's abstract MethodX(). Not a Book case; the
# Book's comment at final.versetest:121 qualifies the two methods
# separately, which would leave the interface's unmet here too. OpenVerse
# prints
#   defined
# If UEFN 43.12 refuses it as well, members are keyed by qualifier whatever
# <final> says (the survey's qualified-names cause).
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3591 (L14) "Non-abstract class inherits
# abstract function `MethodX` from `i_y` but does not provide an
# implementation.".
class_x := class:
    MethodX():int = 1

i_y := interface:
    MethodX():int

class_z := class(class_x, i_y) {}

Main():void =
    Print("OVPROBE defined")
