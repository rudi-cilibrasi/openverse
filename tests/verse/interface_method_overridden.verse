# A class that adds an interface implements its method itself (#724): UEFN
# 43.12 (++Fortnite+Release-43.12-CL-60598086) admits it and its Verse VM
# prints "methods 2 1" (followup-book2/final-method-interface-control). A
# class that inherits the interface through its parent gets the parent's
# implementation, as ever.
class_x := class:
    MethodY<final>():int = 1
i_y := interface:
    MethodX():int
class_z := class(class_x, i_y):
    MethodX<override>():int = 2
base_impl := class(i_y):
    MethodX<override>():int = 3
derived := class(base_impl) {}
Main():void =
    Obj := class_z{}
    Print("methods {Obj.MethodX()} {Obj.MethodY()}")
    I:i_y = derived{}
    Print("inherited {I.MethodX()}")
