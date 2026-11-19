# Control of final-method-interface: a class with a <final> method of
# another name and an interface, the interface's method overridden in
# class_z. Not a Book case. OpenVerse prints
#   methods 2 1
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-19) admits it, and its Verse VM prints methods 2 1, as OpenVerse
# does.
class_x := class:
    MethodY<final>():int = 1

i_y := interface:
    MethodX():int

class_z := class(class_x, i_y):
    MethodX<override>():int = 2

Main():void =
    Obj := class_z{}
    Print("OVPROBE methods {Obj.MethodX()} {Obj.MethodY()}")
