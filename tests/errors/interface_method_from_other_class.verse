# expect: class_z inherits the abstract method MethodX from i_y and does not implement it
# A class's method does not implement an interface's method of its name
# that a subclass adds (#724): it is qualified by where it is introduced,
# (class_x:)MethodX, not (i_y:)MethodX. UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086) refuses class_z with error 3591,
# "Non-abstract class inherits abstract function `MethodX` from `i_y` but
# does not provide an implementation" (followup-book2/final-method-interface-nonfinal).
class_x := class:
    MethodX():int = 1
i_y := interface:
    MethodX():int
class_z := class(class_x, i_y) {}
Main():void = Print("defined")
