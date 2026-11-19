# Control of final-method-interface: a class with a <final> method of
# another name and an interface, the interface's method overridden in
# class_z. Not a Book case. OpenVerse prints
#   methods 2 1
class_x := class:
    MethodY<final>():int = 1

i_y := interface:
    MethodX():int

class_z := class(class_x, i_y):
    MethodX<override>():int = 2

Main():void =
    Obj := class_z{}
    Print("OVPROBE methods {Obj.MethodX()} {Obj.MethodY()}")
