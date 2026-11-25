# expect: class_z inherits the abstract method MethodX from i_y and does not implement it
# The same with a <final> method (#724): the Book's tests,
# Attributes/final.versetest:125 (3591, "qualified separately"); UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086) refuses it with 3591
# (followup-book2/final-method-interface).
class_x := class:
    MethodX<final>():int = 1
i_y := interface:
    MethodX():int
class_z := class(class_x, i_y) {}
Main():void = Print("defined")
